; RUN: llc < %s -mtriple=ve-unknown-unknown | FileCheck %s

define i64 @func1(i64, i32) {
; CHECK-LABEL: func1:
; CHECK:       .LBB{{[0-9]+}}_2:
; CHECK-NEXT:    srl %s2, %s0, %s1
; CHECK-NEXT:    lea %s3, 64
; CHECK-NEXT:    subs.w.sx %s1, %s3, %s1
; CHECK-NEXT:    sll %s0, %s0, %s1
; CHECK-NEXT:    or %s0, %s0, %s2
; CHECK-NEXT:    or %s11, 0, %s9
  %3 = zext i32 %1 to i64
  %4 = lshr i64 %0, %3
  %5 = sub nsw i32 64, %1
  %6 = zext i32 %5 to i64
  %7 = shl i64 %0, %6
  %8 = or i64 %7, %4
  ret i64 %8
}

define i32 @func2(i32, i32) {
; CHECK-LABEL: func2:
; CHECK:       .LBB{{[0-9]+}}_2:
; CHECK-NEXT:    # kill: def $sw0 killed $sw0 def $sx0
; CHECK-NEXT:    and %s2, %s0, (32)0
; CHECK-NEXT:    srl %s2, %s2, %s1
; CHECK-NEXT:    subs.w.sx %s1, 32, %s1
; CHECK-NEXT:    sla.w.sx %s0, %s0, %s1
; CHECK-NEXT:    or %s0, %s0, %s2
; CHECK-NEXT:    or %s11, 0, %s9
  %3 = lshr i32 %0, %1
  %4 = sub nsw i32 32, %1
  %5 = shl i32 %0, %4
  %6 = or i32 %5, %3
  ret i32 %6
}
