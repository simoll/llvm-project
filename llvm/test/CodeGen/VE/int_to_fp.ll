; RUN: llc < %s -mtriple=ve-unknown-unknown | FileCheck %s

; Function Attrs: norecurse nounwind readnone
define float @c2f(i8 signext %a) {
; CHECK-LABEL: c2f:
; CHECK:       .LBB{{[0-9]+}}_2:
; CHECK-NEXT:    cvt.s.w %s0, %s0
; CHECK-NEXT:    or %s11, 0, %s9
entry:
  %conv = sitofp i8 %a to float
  ret float %conv
}

; Function Attrs: norecurse nounwind readnone
define float @s2f(i16 signext %a) {
; CHECK-LABEL: s2f:
; CHECK:       .LBB{{[0-9]+}}_2:
; CHECK-NEXT:    cvt.s.w %s0, %s0
; CHECK-NEXT:    or %s11, 0, %s9
entry:
  %conv = sitofp i16 %a to float
  ret float %conv
}

; Function Attrs: norecurse nounwind readnone
define float @i2f(i32 %a) {
; CHECK-LABEL: i2f:
; CHECK:       .LBB{{[0-9]+}}_2:
; CHECK-NEXT:    cvt.s.w %s0, %s0
; CHECK-NEXT:    or %s11, 0, %s9
entry:
  %conv = sitofp i32 %a to float
  ret float %conv
}

; Function Attrs: norecurse nounwind readnone
define float @l2f(i64 %a) {
; CHECK-LABEL: l2f:
; CHECK:       .LBB{{[0-9]+}}_2:
; CHECK-NEXT:    cvt.d.l %s0, %s0
; CHECK-NEXT:    cvt.s.d %s0, %s0
; CHECK-NEXT:    or %s11, 0, %s9
entry:
  %conv = sitofp i64 %a to float
  ret float %conv
}

; Function Attrs: norecurse nounwind readnone
define float @i1282f(i128 %a) {
; CHECK-LABEL: i1282f:
; CHECK:       .LBB{{[0-9]+}}_2:
; CHECK-NEXT:    lea %s2, __floattisf@lo
; CHECK-NEXT:    and %s2, %s2, (32)0
; CHECK-NEXT:    lea.sl %s12, __floattisf@hi(%s2)
; CHECK-NEXT:    bsic %lr, (,%s12)
; CHECK-NEXT:    or %s11, 0, %s9
  %r = sitofp i128 %a to float
  ret float %r
}

; Function Attrs: norecurse nounwind readnone
define float @uc2f(i8 zeroext %a) {
; CHECK-LABEL: uc2f:
; CHECK:       .LBB{{[0-9]+}}_2:
; CHECK-NEXT:    cvt.s.w %s0, %s0
; CHECK-NEXT:    or %s11, 0, %s9
entry:
  %conv = uitofp i8 %a to float
  ret float %conv
}

; Function Attrs: norecurse nounwind readnone
define float @us2f(i16 zeroext %a) {
; CHECK-LABEL: us2f:
; CHECK:       .LBB{{[0-9]+}}_2:
; CHECK-NEXT:    cvt.s.w %s0, %s0
; CHECK-NEXT:    or %s11, 0, %s9
entry:
  %conv = uitofp i16 %a to float
  ret float %conv
}

; Function Attrs: norecurse nounwind readnone
define float @ui2f(i32 %a) {
; CHECK-LABEL: ui2f:
; CHECK:       .LBB{{[0-9]+}}_2:
; CHECK-NEXT:    adds.w.zx %s0, %s0, (0)1
; CHECK-NEXT:    cvt.d.l %s0, %s0
; CHECK-NEXT:    cvt.s.d %s0, %s0
; CHECK-NEXT:    or %s11, 0, %s9
entry:
  %conv = uitofp i32 %a to float
  ret float %conv
}

; Function Attrs: norecurse nounwind readnone
define float @ul2f(i64 %a) {
; CHECK-LABEL: ul2f:
; CHECK:       .LBB{{[0-9]+}}_2:
; CHECK-NEXT:    or %s1, 0, (0)1
; CHECK-NEXT:    cmps.l %s2, %s0, %s1
; CHECK-NEXT:    cvt.d.l %s1, %s0
; CHECK-NEXT:    cvt.s.d %s1, %s1
; CHECK-NEXT:    srl %s3, %s0, 1
; CHECK-NEXT:    and %s0, 1, %s0
; CHECK-NEXT:    or %s0, %s0, %s3
; CHECK-NEXT:    cvt.d.l %s0, %s0
; CHECK-NEXT:    cvt.s.d %s0, %s0
; CHECK-NEXT:    fadd.s %s0, %s0, %s0
; CHECK-NEXT:    cmov.l.lt %s1, %s0, %s2
; CHECK-NEXT:    or %s0, 0, %s1
; CHECK-NEXT:    or %s11, 0, %s9
entry:
  %conv = uitofp i64 %a to float
  ret float %conv
}

; Function Attrs: norecurse nounwind readnone
define float @ui1282f(i128 %a) {
; CHECK-LABEL: ui1282f:
; CHECK:       .LBB{{[0-9]+}}_2:
; CHECK-NEXT:    lea %s2, __floatuntisf@lo
; CHECK-NEXT:    and %s2, %s2, (32)0
; CHECK-NEXT:    lea.sl %s12, __floatuntisf@hi(%s2)
; CHECK-NEXT:    bsic %lr, (,%s12)
; CHECK-NEXT:    or %s11, 0, %s9
  %r = uitofp i128 %a to float
  ret float %r
}

; Function Attrs: norecurse nounwind readnone
define double @c2d(i8 signext %a) {
; CHECK-LABEL: c2d:
; CHECK:       .LBB{{[0-9]+}}_2:
; CHECK-NEXT:    cvt.d.w %s0, %s0
; CHECK-NEXT:    or %s11, 0, %s9
entry:
  %conv = sitofp i8 %a to double
  ret double %conv
}

; Function Attrs: norecurse nounwind readnone
define double @s2d(i16 signext %a) {
; CHECK-LABEL: s2d:
; CHECK:       .LBB{{[0-9]+}}_2:
; CHECK-NEXT:    cvt.d.w %s0, %s0
; CHECK-NEXT:    or %s11, 0, %s9
entry:
  %conv = sitofp i16 %a to double
  ret double %conv
}

; Function Attrs: norecurse nounwind readnone
define double @i2d(i32 %a) {
; CHECK-LABEL: i2d:
; CHECK:       .LBB{{[0-9]+}}_2:
; CHECK-NEXT:    cvt.d.w %s0, %s0
; CHECK-NEXT:    or %s11, 0, %s9
entry:
  %conv = sitofp i32 %a to double
  ret double %conv
}

; Function Attrs: norecurse nounwind readnone
define double @l2d(i64 %a) {
; CHECK-LABEL: l2d:
; CHECK:       .LBB{{[0-9]+}}_2:
; CHECK-NEXT:    cvt.d.l %s0, %s0
; CHECK-NEXT:    or %s11, 0, %s9
entry:
  %conv = sitofp i64 %a to double
  ret double %conv
}

; Function Attrs: norecurse nounwind readnone
define double @i1282d(i128 %a) {
; CHECK-LABEL: i1282d:
; CHECK:       .LBB{{[0-9]+}}_2:
; CHECK-NEXT:    lea %s2, __floattidf@lo
; CHECK-NEXT:    and %s2, %s2, (32)0
; CHECK-NEXT:    lea.sl %s12, __floattidf@hi(%s2)
; CHECK-NEXT:    bsic %lr, (,%s12)
; CHECK-NEXT:    or %s11, 0, %s9
  %r = sitofp i128 %a to double
  ret double %r
}

; Function Attrs: norecurse nounwind readnone
define double @uc2d(i8 zeroext %a) {
; CHECK-LABEL: uc2d:
; CHECK:       .LBB{{[0-9]+}}_2:
; CHECK-NEXT:    cvt.d.w %s0, %s0
; CHECK-NEXT:    or %s11, 0, %s9
entry:
  %conv = uitofp i8 %a to double
  ret double %conv
}

; Function Attrs: norecurse nounwind readnone
define double @us2d(i16 zeroext %a) {
; CHECK-LABEL: us2d:
; CHECK:       .LBB{{[0-9]+}}_2:
; CHECK-NEXT:    cvt.d.w %s0, %s0
; CHECK-NEXT:    or %s11, 0, %s9
entry:
  %conv = uitofp i16 %a to double
  ret double %conv
}

; Function Attrs: norecurse nounwind readnone
define double @ui2d(i32 %a) {
; CHECK-LABEL: ui2d:
; CHECK:       .LBB{{[0-9]+}}_2:
; CHECK-NEXT:    adds.w.zx %s0, %s0, (0)1
; CHECK-NEXT:    cvt.d.l %s0, %s0
; CHECK-NEXT:    or %s11, 0, %s9
entry:
  %conv = uitofp i32 %a to double
  ret double %conv
}

; Function Attrs: norecurse nounwind readnone
define double @ul2d(i64 %a) {
; CHECK-LABEL: ul2d:
; CHECK:       .LBB{{[0-9]+}}_2:
; CHECK-NEXT:    srl %s1, %s0, 32
; CHECK-NEXT:    lea.sl %s2, 1160773632
; CHECK-NEXT:    or %s1, %s1, %s2
; CHECK-NEXT:    lea %s2, 1048576
; CHECK-NEXT:    lea.sl %s2, -986710016(%s2)
; CHECK-NEXT:    fadd.d %s1, %s1, %s2
; CHECK-NEXT:    lea %s2, -1
; CHECK-NEXT:    and %s2, %s2, (32)0
; CHECK-NEXT:    and %s0, %s0, %s2
; CHECK-NEXT:    lea.sl %s2, 1127219200
; CHECK-NEXT:    or %s0, %s0, %s2
; CHECK-NEXT:    fadd.d %s0, %s0, %s1
; CHECK-NEXT:    or %s11, 0, %s9
entry:
  %conv = uitofp i64 %a to double
  ret double %conv
}

; Function Attrs: norecurse nounwind readnone
define double @ui1282d(i128 %a) {
; CHECK-LABEL: ui1282d:
; CHECK:       .LBB{{[0-9]+}}_2:
; CHECK-NEXT:    lea %s2, __floatuntidf@lo
; CHECK-NEXT:    and %s2, %s2, (32)0
; CHECK-NEXT:    lea.sl %s12, __floatuntidf@hi(%s2)
; CHECK-NEXT:    bsic %lr, (,%s12)
; CHECK-NEXT:    or %s11, 0, %s9
  %r = uitofp i128 %a to double
  ret double %r
}

; Function Attrs: norecurse nounwind readnone
define fp128 @c2q(i8 signext %a) {
; CHECK-LABEL: c2q:
; CHECK:       .LBB{{[0-9]+}}_2:
; CHECK-NEXT:    cvt.d.w %s0, %s0
; CHECK-NEXT:    cvt.q.d %s0, %s0
; CHECK-NEXT:    or %s11, 0, %s9
entry:
  %conv = sitofp i8 %a to fp128
  ret fp128 %conv
}

; Function Attrs: norecurse nounwind readnone
define fp128 @s2q(i16 signext %a) {
; CHECK-LABEL: s2q:
; CHECK:       .LBB{{[0-9]+}}_2:
; CHECK-NEXT:    cvt.d.w %s0, %s0
; CHECK-NEXT:    cvt.q.d %s0, %s0
; CHECK-NEXT:    or %s11, 0, %s9
entry:
  %conv = sitofp i16 %a to fp128
  ret fp128 %conv
}

; Function Attrs: norecurse nounwind readnone
define fp128 @i2q(i32 %a) {
; CHECK-LABEL: i2q:
; CHECK:       .LBB{{[0-9]+}}_2:
; CHECK-NEXT:    cvt.d.w %s0, %s0
; CHECK-NEXT:    cvt.q.d %s0, %s0
; CHECK-NEXT:    or %s11, 0, %s9
entry:
  %conv = sitofp i32 %a to fp128
  ret fp128 %conv
}

; Function Attrs: norecurse nounwind readnone
define fp128 @l2q(i64 %a) {
; CHECK-LABEL: l2q:
; CHECK:       .LBB{{[0-9]+}}_2:
; CHECK-NEXT:    cvt.d.l %s0, %s0
; CHECK-NEXT:    cvt.q.d %s0, %s0
; CHECK-NEXT:    or %s11, 0, %s9
entry:
  %conv = sitofp i64 %a to fp128
  ret fp128 %conv
}

; Function Attrs: norecurse nounwind readnone
define fp128 @i1282q(i128) {
; CHECK-LABEL: i1282q:
; CHECK:       .LBB{{[0-9]+}}_2:
; CHECK-NEXT:    lea %s2, __floattitf@lo
; CHECK-NEXT:    and %s2, %s2, (32)0
; CHECK-NEXT:    lea.sl %s12, __floattitf@hi(%s2)
; CHECK-NEXT:    bsic %lr, (,%s12)
; CHECK-NEXT:    or %s11, 0, %s9
  %2 = sitofp i128 %0 to fp128
  ret fp128 %2
}

; Function Attrs: norecurse nounwind readnone
define fp128 @uc2q(i8 zeroext %a) {
; CHECK-LABEL: uc2q:
; CHECK:       .LBB{{[0-9]+}}_2:
; CHECK-NEXT:    cvt.d.w %s0, %s0
; CHECK-NEXT:    cvt.q.d %s0, %s0
; CHECK-NEXT:    or %s11, 0, %s9
entry:
  %conv = uitofp i8 %a to fp128
  ret fp128 %conv
}

; Function Attrs: norecurse nounwind readnone
define fp128 @us2q(i16 zeroext %a) {
; CHECK-LABEL: us2q:
; CHECK:       .LBB{{[0-9]+}}_2:
; CHECK-NEXT:    cvt.d.w %s0, %s0
; CHECK-NEXT:    cvt.q.d %s0, %s0
; CHECK-NEXT:    or %s11, 0, %s9
entry:
  %conv = uitofp i16 %a to fp128
  ret fp128 %conv
}

; Function Attrs: norecurse nounwind readnone
define fp128 @ui2q(i32 %a) {
; CHECK-LABEL: ui2q:
; CHECK:       .LBB{{[0-9]+}}_2:
; CHECK-NEXT:    adds.w.zx %s0, %s0, (0)1
; CHECK-NEXT:    cvt.d.l %s0, %s0
; CHECK-NEXT:    cvt.q.d %s0, %s0
; CHECK-NEXT:    or %s11, 0, %s9
entry:
  %conv = uitofp i32 %a to fp128
  ret fp128 %conv
}

; Function Attrs: norecurse nounwind readnone
define fp128 @ul2q(i64 %a) {
; CHECK-LABEL: ul2q:
; CHECK:       .LBB{{[0-9]+}}_2:
; CHECK-NEXT:    srl %s1, %s0, 61
; CHECK-NEXT:    and %s1, 4, %s1
; CHECK-NEXT:    lea %s2, .LCPI28_0@lo
; CHECK-NEXT:    and %s2, %s2, (32)0
; CHECK-NEXT:    lea.sl %s2, .LCPI28_0@hi(%s2)
; CHECK-NEXT:    adds.l %s1, %s2, %s1
; CHECK-NEXT:    ldu %s1, (,%s1)
; CHECK-NEXT:    cvt.q.s %s2, %s1
; CHECK-NEXT:    cvt.d.l %s0, %s0
; CHECK-NEXT:    cvt.q.d %s0, %s0
; CHECK-NEXT:    fadd.q %s0, %s0, %s2
; CHECK-NEXT:    or %s11, 0, %s9
entry:
  %conv = uitofp i64 %a to fp128
  ret fp128 %conv
}

; Function Attrs: norecurse nounwind readnone
define fp128 @ui1282q(i128) {
; CHECK-LABEL: ui1282q:
; CHECK:       .LBB{{[0-9]+}}_2:
; CHECK-NEXT:    lea %s2, __floatuntitf@lo
; CHECK-NEXT:    and %s2, %s2, (32)0
; CHECK-NEXT:    lea.sl %s12, __floatuntitf@hi(%s2)
; CHECK-NEXT:    bsic %lr, (,%s12)
; CHECK-NEXT:    or %s11, 0, %s9
  %2 = uitofp i128 %0 to fp128
  ret fp128 %2
}
