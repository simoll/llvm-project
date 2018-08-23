//===--------------------- Scheduler.h ------------------------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
/// \file
///
/// A scheduler for Processor Resource Units and Processor Resource Groups.
///
//===----------------------------------------------------------------------===//

#ifndef LLVM_TOOLS_LLVM_MCA_SCHEDULER_H
#define LLVM_TOOLS_LLVM_MCA_SCHEDULER_H

#include "HardwareUnit.h"
#include "Instruction.h"
#include "LSUnit.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/MC/MCSubtargetInfo.h"
#include <map>

namespace mca {

/// Used to notify the internal state of a processor resource.
///
/// A processor resource is available if it is not reserved, and there are
/// available slots in the buffer.  A processor resource is unavailable if it
/// is either reserved, or the associated buffer is full. A processor resource
/// with a buffer size of -1 is always available if it is not reserved.
///
/// Values of type ResourceStateEvent are returned by method
/// ResourceState::isBufferAvailable(), which is used to query the internal
/// state of a resource.
///
/// The naming convention for resource state events is:
///  * Event names start with prefix RS_
///  * Prefix RS_ is followed by a string describing the actual resource state.
enum ResourceStateEvent {
  RS_BUFFER_AVAILABLE,
  RS_BUFFER_UNAVAILABLE,
  RS_RESERVED
};

/// A descriptor for processor resources.
///
/// Each object of class ResourceState is associated to a specific processor
/// resource. There is an instance of this class for every processor resource
/// defined by the scheduling model.
/// A ResourceState dynamically tracks the availability of units of a processor
/// resource. For example, the ResourceState of a ProcResGroup tracks the
/// availability of resource units which are part of the group.
///
/// Internally, ResourceState uses a round-robin selector to identify
/// which unit of the group shall be used next.
class ResourceState {
  // Index to the MCProcResourceDesc in the processor Model.
  unsigned ProcResourceDescIndex;
  // A resource mask. This is generated by the tool with the help of
  // function `mca::createProcResourceMasks' (see Support.h).
  uint64_t ResourceMask;

  // A ProcResource can specify a number of units. For the purpose of dynamic
  // scheduling, a processor resource with more than one unit behaves like a
  // group. This field has one bit set for every unit/resource that is part of
  // the group.
  // For groups, this field defaults to 'ResourceMask'. For non-group
  // resources, the number of bits set in this mask is equivalent to the
  // number of units (i.e. field 'NumUnits' in 'ProcResourceUnits').
  uint64_t ResourceSizeMask;

  // A simple round-robin selector for processor resources.
  // Each bit of the mask identifies a sub resource within this group.
  //
  // As an example, lets assume that this ResourceState describes a
  // processor resource group composed of the following three units:
  //   ResourceA -- 0b001
  //   ResourceB -- 0b010
  //   ResourceC -- 0b100
  //
  // Each unit is identified by a ResourceMask which always contains a
  // single bit set. Field NextInSequenceMask is initially set to value
  // 0xb111. That value is obtained by OR'ing the resource masks of
  // processor resource that are part of the group.
  //
  //   NextInSequenceMask  -- 0b111
  //
  // Field NextInSequenceMask is used by the resource manager (i.e.
  // an object of class ResourceManager) to select the "next available resource"
  // from the set. The algorithm would prioritize resources with a bigger
  // ResourceMask value.
  //
  // In this example, there are three resources in the set, and 'ResourceC'
  // has the highest mask value. The round-robin selector would firstly select
  //  'ResourceC', then 'ResourceB', and eventually 'ResourceA'.
  //
  // When a resource R is used, its corresponding bit is cleared from the set.
  //
  // Back to the example:
  // If 'ResourceC' is selected, then the new value of NextInSequenceMask
  // becomes 0xb011.
  //
  // When NextInSequenceMask becomes zero, it is reset to its original value
  // (in this example, that value would be 0b111).
  uint64_t NextInSequenceMask;

  // Some instructions can only be issued on very specific pipeline resources.
  // For those instructions, we know exactly which resource would be consumed
  // without having to dynamically select it using field 'NextInSequenceMask'.
  //
  // The resource mask bit associated to the (statically) selected
  // processor resource is still cleared from the 'NextInSequenceMask'.
  // If that bit was already zero in NextInSequenceMask, then we update
  // mask 'RemovedFromNextInSequence'.
  //
  // When NextInSequenceMask is reset back to its initial value, the algorithm
  // removes any bits which are set in RemoveFromNextInSequence.
  uint64_t RemovedFromNextInSequence;

  // A mask of ready units.
  uint64_t ReadyMask;

  // Buffered resources will have this field set to a positive number bigger
  // than 0. A buffered resource behaves like a separate reservation station
  // implementing its own buffer for out-of-order execution.
  // A buffer of 1 is for units that force in-order execution.
  // A value of 0 is treated specially. In particular, a resource with
  // A BufferSize = 0 is for an in-order issue/dispatch resource.
  // That means, this resource is reserved starting from the dispatch event,
  // until all the "resource cycles" are consumed after the issue event.
  // While this resource is reserved, no other instruction may be dispatched.
  int BufferSize;

  // Available slots in the buffer (zero, if this is not a buffered resource).
  unsigned AvailableSlots;

  // True if this is resource is currently unavailable.
  // An instruction may "reserve" a resource for a number of cycles.
  // During those cycles, the reserved resource cannot be used for other
  // instructions, even if the ReadyMask is set.
  bool Unavailable;

  bool isSubResourceReady(uint64_t ID) const { return ReadyMask & ID; }

  /// Returns the mask identifier of the next available resource in the set.
  uint64_t getNextInSequence() const {
    assert(NextInSequenceMask);
    return llvm::PowerOf2Floor(NextInSequenceMask);
  }

  /// Returns the mask of the next available resource within the set,
  /// and updates the resource selector.
  void updateNextInSequence() {
    NextInSequenceMask ^= getNextInSequence();
    if (!NextInSequenceMask)
      NextInSequenceMask = ResourceSizeMask;
  }

  uint64_t computeResourceSizeMaskForGroup(uint64_t ResourceMask) {
    assert(llvm::countPopulation(ResourceMask) > 1);
    return ResourceMask ^ llvm::PowerOf2Floor(ResourceMask);
  }

public:
  ResourceState(const llvm::MCProcResourceDesc &Desc, unsigned Index,
                uint64_t Mask)
      : ProcResourceDescIndex(Index), ResourceMask(Mask) {
    bool IsAGroup = llvm::countPopulation(ResourceMask) > 1;
    ResourceSizeMask = IsAGroup ? computeResourceSizeMaskForGroup(ResourceMask)
                                : ((1ULL << Desc.NumUnits) - 1);
    NextInSequenceMask = ResourceSizeMask;
    RemovedFromNextInSequence = 0;
    ReadyMask = ResourceSizeMask;
    BufferSize = Desc.BufferSize;
    AvailableSlots = BufferSize == -1 ? 0U : static_cast<unsigned>(BufferSize);
    Unavailable = false;
  }

  unsigned getProcResourceID() const { return ProcResourceDescIndex; }
  uint64_t getResourceMask() const { return ResourceMask; }
  int getBufferSize() const { return BufferSize; }

  bool isBuffered() const { return BufferSize > 0; }
  bool isInOrder() const { return BufferSize == 1; }
  bool isADispatchHazard() const { return BufferSize == 0; }
  bool isReserved() const { return Unavailable; }

  void setReserved() { Unavailable = true; }
  void clearReserved() { Unavailable = false; }

  // A resource is ready if it is not reserved, and if there are enough
  // available units.
  // If a resource is also a dispatch hazard, then we don't check if
  // it is reserved because that check would always return true.
  // A resource marked as "dispatch hazard" is always reserved at
  // dispatch time. When this method is called, the assumption is that
  // the user of this resource has been already dispatched.
  bool isReady(unsigned NumUnits = 1) const {
    return (!isReserved() || isADispatchHazard()) &&
           llvm::countPopulation(ReadyMask) >= NumUnits;
  }
  bool isAResourceGroup() const {
    return llvm::countPopulation(ResourceMask) > 1;
  }

  bool containsResource(uint64_t ID) const { return ResourceMask & ID; }

  void markSubResourceAsUsed(uint64_t ID) {
    assert(isSubResourceReady(ID));
    ReadyMask ^= ID;
  }

  void releaseSubResource(uint64_t ID) {
    assert(!isSubResourceReady(ID));
    ReadyMask ^= ID;
  }

  unsigned getNumUnits() const {
    return isAResourceGroup() ? 1U : llvm::countPopulation(ResourceSizeMask);
  }

  uint64_t selectNextInSequence();
  void removeFromNextInSequence(uint64_t ID);

  ResourceStateEvent isBufferAvailable() const {
    if (isADispatchHazard() && isReserved())
      return RS_RESERVED;
    if (!isBuffered() || AvailableSlots)
      return RS_BUFFER_AVAILABLE;
    return RS_BUFFER_UNAVAILABLE;
  }

  void reserveBuffer() {
    if (AvailableSlots)
      AvailableSlots--;
  }

  void releaseBuffer() {
    if (BufferSize > 0)
      AvailableSlots++;
    assert(AvailableSlots <= static_cast<unsigned>(BufferSize));
  }

#ifndef NDEBUG
  void dump() const;
#endif
};

/// A resource unit identifier.
///
/// This is used to identify a specific processor resource unit using a pair
/// of indices where the 'first' index is a processor resource mask, and the
/// 'second' index is an index for a "sub-resource" (i.e. unit).
typedef std::pair<uint64_t, uint64_t> ResourceRef;

// First: a MCProcResourceDesc index identifying a buffered resource.
// Second: max number of buffer entries used in this resource.
typedef std::pair<unsigned, unsigned> BufferUsageEntry;

/// A resource manager for processor resource units and groups.
///
/// This class owns all the ResourceState objects, and it is responsible for
/// acting on requests from a Scheduler by updating the internal state of
/// ResourceState objects.
/// This class doesn't know about instruction itineraries and functional units.
/// In future, it can be extended to support itineraries too through the same
/// public interface.
class ResourceManager {
  // The resource manager owns all the ResourceState.
  using UniqueResourceState = std::unique_ptr<ResourceState>;
  std::vector<UniqueResourceState> Resources;

  // Keeps track of which resources are busy, and how many cycles are left
  // before those become usable again.
  llvm::SmallDenseMap<ResourceRef, unsigned> BusyResources;

  // A table to map processor resource IDs to processor resource masks.
  llvm::SmallVector<uint64_t, 8> ProcResID2Mask;

  // Populate resource descriptors.
  void initialize(const llvm::MCSchedModel &SM);

  // Returns the actual resource unit that will be used.
  ResourceRef selectPipe(uint64_t ResourceID);

  void use(const ResourceRef &RR);
  void release(const ResourceRef &RR);

  unsigned getNumUnits(uint64_t ResourceID) const;

public:
  ResourceManager(const llvm::MCSchedModel &SM)
      : ProcResID2Mask(SM.getNumProcResourceKinds()) {
    initialize(SM);
  }

  // Returns RS_BUFFER_AVAILABLE if buffered resources are not reserved, and if
  // there are enough available slots in the buffers.
  ResourceStateEvent canBeDispatched(llvm::ArrayRef<uint64_t> Buffers) const;

  // Return the processor resource identifier associated to this Mask.
  unsigned resolveResourceMask(uint64_t Mask) const;

  // Consume a slot in every buffered resource from array 'Buffers'. Resource
  // units that are dispatch hazards (i.e. BufferSize=0) are marked as reserved.
  void reserveBuffers(llvm::ArrayRef<uint64_t> Buffers);

  // Release buffer entries previously allocated by method reserveBuffers.
  void releaseBuffers(llvm::ArrayRef<uint64_t> Buffers);

  // Reserve a processor resource. A reserved resource is not available for
  // instruction issue until it is released.
  void reserveResource(uint64_t ResourceID);

  // Release a previously reserved processor resource.
  void releaseResource(uint64_t ResourceID);

  // Returns true if all resources are in-order, and there is at least one
  // resource which is a dispatch hazard (BufferSize = 0).
  bool mustIssueImmediately(const InstrDesc &Desc) const;

  bool canBeIssued(const InstrDesc &Desc) const;

  void issueInstruction(
      const InstrDesc &Desc,
      llvm::SmallVectorImpl<std::pair<ResourceRef, double>> &Pipes);

  void cycleEvent(llvm::SmallVectorImpl<ResourceRef> &ResourcesFreed);

#ifndef NDEBUG
  void dump() const {
    for (const UniqueResourceState &Resource : Resources)
      Resource->dump();
  }
#endif
}; // namespace mca

/// Class Scheduler is responsible for issuing instructions to pipeline
/// resources.
///
/// Internally, it delegates to a ResourceManager the management of processor
/// resources. This class is also responsible for tracking the progress of
/// instructions from the dispatch stage, until the write-back stage.
///
/// An instruction dispatched to the Scheduler is initially placed into either
/// the 'WaitSet' or the 'ReadySet' depending on the availability of the input
/// operands.
///
/// An instruction is moved from the WaitSet to the ReadySet when register
/// operands become available, and all memory dependencies are met.
/// Instructions that are moved from the WaitSet to the ReadySet transition
/// in state from 'IS_AVAILABLE' to 'IS_READY'.
///
/// On every cycle, the Scheduler checks if it can promote instructions from the
/// WaitSet to the ReadySet.
///
/// An Instruction is moved from the ReadySet the `IssuedSet` when it is issued
/// to a (one or more) pipeline(s). This event also causes an instruction state
/// transition (i.e. from state IS_READY, to state IS_EXECUTING). An Instruction
/// leaves the IssuedSet when it reaches the write-back stage.
class Scheduler : public HardwareUnit {
  const llvm::MCSchedModel &SM;
  LSUnit *LSU;

  // Hardware resources that are managed by this scheduler.
  std::unique_ptr<ResourceManager> Resources;

  std::vector<InstRef> WaitSet;
  std::vector<InstRef> ReadySet;
  std::vector<InstRef> IssuedSet;

  /// Issue an instruction without updating the ready queue.
  void issueInstructionImpl(
      InstRef &IR,
      llvm::SmallVectorImpl<std::pair<ResourceRef, double>> &Pipes);

public:
  Scheduler(const llvm::MCSchedModel &Model, LSUnit *Lsu)
      : SM(Model), LSU(Lsu), Resources(llvm::make_unique<ResourceManager>(SM)) {
  }

  // Stalls generated by the scheduler.
  enum Status {
    SC_AVAILABLE,
    SC_LOAD_QUEUE_FULL,
    SC_STORE_QUEUE_FULL,
    SC_BUFFERS_FULL,
    SC_DISPATCH_GROUP_STALL,
  };

  /// Check if the instruction in 'IR' can be dispatched and returns an answer
  /// in the form of a Status value.
  ///
  /// The DispatchStage is responsible for querying the Scheduler before
  /// dispatching new instructions. This routine is used for performing such
  /// a query.  If the instruction 'IR' can be dispatched, then true is
  /// returned, otherwise false is returned with Event set to the stall type.
  /// Internally, it also checks if the load/store unit is available.
  Status isAvailable(const InstRef &IR) const;

  /// Reserves buffer and LSUnit queue resources that are necessary to issue
  /// this instruction.
  ///
  /// Returns true if instruction IR is ready to be issued to the underlying
  /// pipelines. Note that this operation cannot fail; it assumes that a
  /// previous call to method `isAvailable(IR)` returned `SC_AVAILABLE`.
  void dispatch(const InstRef &IR);

  /// Returns true if IR is ready to be executed by the underlying pipelines.
  /// This method assumes that IR has been previously dispatched.
  bool isReady(const InstRef &IR) const;

  /// Issue an instruction.  The Used container is populated with
  /// the resource objects consumed on behalf of issuing this instruction.
  void issueInstruction(InstRef &IR,
                   llvm::SmallVectorImpl<std::pair<ResourceRef, double>> &Used);

  /// Returns true if IR has to be issued immediately, or if IR is a zero
  /// latency instruction.
  bool mustIssueImmediately(const InstRef &IR) const;

  /// Update the resources managed by the scheduler.
  /// This routine is to be called at the start of a new cycle, and is
  /// responsible for updating scheduler resources.  Resources are released
  /// once they have been fully consumed.
  void reclaimSimulatedResources(llvm::SmallVectorImpl<ResourceRef> &Freed);

  /// Move instructions from the WaitSet to the ReadySet if input operands
  /// are all available.
  void promoteToReadySet(llvm::SmallVectorImpl<InstRef> &Ready);

  /// Update the ready queue.
  void updatePendingQueue(llvm::SmallVectorImpl<InstRef> &Ready);

  /// Update the issued queue.
  void updateIssuedSet(llvm::SmallVectorImpl<InstRef> &Executed);

  /// Obtain the processor's resource identifier for the given
  /// resource mask.
  unsigned getResourceID(uint64_t Mask) {
    return Resources->resolveResourceMask(Mask);
  }

  /// Select the next instruction to issue from the ReadySet.
  /// This method gives priority to older instructions.
  InstRef select();

#ifndef NDEBUG
  // Update the ready queues.
  void dump() const;

  // This routine performs a sanity check.  This routine should only be called
  // when we know that 'IR' is not in the scheduler's instruction queues.
  void sanityCheck(const InstRef &IR) const {
    assert(llvm::find(WaitSet, IR) == WaitSet.end());
    assert(llvm::find(ReadySet, IR) == ReadySet.end());
    assert(llvm::find(IssuedSet, IR) == IssuedSet.end());
  }
#endif // !NDEBUG
};
} // namespace mca

#endif // LLVM_TOOLS_LLVM_MCA_SCHEDULER_H
