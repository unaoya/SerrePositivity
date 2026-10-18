module

public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero

/-!
概要：三角関手の零対象への核は三角部分圏である。
方針：零対象のシフト保存と標準三角形の零対象判定を逆像へ移す。
規約：局所化同値や compact 生成を仮定しない。
使われ方：Neeman 1992 Thm 2.1、TT 3.19・8.1 の台つき導来部分圏。
-/

@[expose] public section
noncomputable section
open CategoryTheory Limits Pretriangulated
namespace SerrePositivity.KST.DerivedGeometry

variable {C : Type*} [Category* C] [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {D : Type*} [Category* D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/--
概要：零対象の対象条件は同型で不変。
方針：同型による零対象性の同値を使う。
規約：同型閉包を別に選ばない。
使われ方：Neeman 1992 Thm 2.1 の核の三角構造。
-/
instance zeroObjects_closedUnderIso : ObjectProperty.IsClosedUnderIsomorphisms (IsZero (C := C)) where
  of_iso e h := e.isZero_iff.mp h

/--
概要：零対象の対象条件は整数シフトで安定。
方針：各シフト関手による零対象の保存を使う。
規約：標準シフトを保持する。
使われ方：Neeman 1992 Thm 2.1 の核の三角構造。
-/
instance zeroObjects_isStableUnderShift : ObjectProperty.IsStableUnderShift (IsZero (C := C)) ℤ where
  isStableUnderShiftBy n := .mk (fun X h => (shiftFunctor C n).map_isZero h)

/--
概要：零対象からなる対象条件は三角部分圏。
方針：両端が零の区別三角形の中項も零であることを使う。
規約：同型閉包を含む Mathlib の三角部分圏の条件で述べる。
使われ方：Neeman 1992 Thm 2.1、TT 3.19 の核の三角構造。
-/
instance zeroObjects_isTriangulated : ObjectProperty.IsTriangulated (IsZero (C := C)) where
  toIsTriangulatedClosed₂ := .mk' (fun T hT h₁ h₃ =>
    T.isZero₂_of_isZero₁₃ hT h₁ h₃)

/--
概要：三角関手の核は三角部分圏。
方針：零対象の三角部分圏の逆像を取る。
規約：核は像が実際に零対象になる対象条件。
使われ方：Neeman 1992 Thm 2.1、TT 3.19・8.1 の局所化。
-/
instance triangulatedKernel_isTriangulated (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] :
    F.kernel.IsTriangulated :=
  inferInstanceAs ((ObjectProperty.inverseImage (IsZero (C := D)) F).IsTriangulated)

end SerrePositivity.KST.DerivedGeometry
