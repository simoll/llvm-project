; NOTE: Assertions have been autogenerated by utils/update_llc_test_checks.py
; RUN: llc -global-isel -mtriple=amdgcn--amdhsa -mcpu=gfx1010 -mattr=+wavefrontsize32,-wavefrontsize64 -verify-machineinstrs < %s | FileCheck -check-prefix=GCN %s

define amdgpu_kernel void @test_wave32(i32 %arg0, [8 x i32], i32 %saved) {
; GCN-LABEL: test_wave32:
; GCN:       ; %bb.0: ; %entry
; GCN-NEXT:    s_clause 0x1
; GCN-NEXT:    s_load_dword s0, s[4:5], 0x0
; GCN-NEXT:    s_load_dword s1, s[4:5], 0x24
; GCN-NEXT:    ; implicit-def: $vcc_hi
; GCN-NEXT:    s_waitcnt lgkmcnt(0)
; GCN-NEXT:    s_cmp_eq_u32 s0, 0
; GCN-NEXT:    s_cselect_b32 s0, 1, 0
; GCN-NEXT:    s_and_b32 s0, 1, s0
; GCN-NEXT:    v_cmp_ne_u32_e64 s0, 0, s0
; GCN-NEXT:    s_or_b32 s0, s0, s1
; GCN-NEXT:    v_mov_b32_e32 v0, s0
; GCN-NEXT:    global_store_dword v[0:1], v0, off
; GCN-NEXT:    s_endpgm
entry:
  %cond = icmp eq i32 %arg0, 0
  %break = call i32 @llvm.amdgcn.if.break.i32(i1 %cond, i32 %saved)
  store volatile i32 %break, i32 addrspace(1)* undef
  ret void
}

declare i32 @llvm.amdgcn.if.break.i32(i1, i32)
