module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Algebra.Category.Ring.Constructions

/-!
概要：実際のスキームの底変換のアフィン交叉上で、構造層の切断を pushout と比較する。
方針：Mathlib の canonical な pushoutSection のアフィンの場合の同型性を用いる。
規約：平坦性を仮定しない。閉厚化にも同じ写像を使う。
使われ方：標準開 Čech の底変換・閉厚化・模型の遷移の実際の切断との照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
variable {X Y S T : Scheme.{u}} {f : T ⟶ S} {g : Y ⟶ X} {iX : X ⟶ S} {iY : Y ⟶ T}
variable (H : IsPullback g iY iX f)
variable {US : S.Opens} {UT : T.Opens} {UX : X.Opens} {UY : Y.Opens}
variable (hUST : UT ≤ f ⁻¹ᵁ US) (hUSX : UX ≤ iX ⁻¹ᵁ US)
variable (hUY : UY = g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT)
variable (hUS : IsAffineOpen US) (hUT : IsAffineOpen UT) (hUX : IsAffineOpen UX)

/-- アフィン交叉上の実際の切断は、三つの切断環の canonical な pushout と同型。 -/
def schemeAffinePullbackSectionIso :
    pushout (iX.appLE US UX hUSX) (f.appLE US UT hUST) ≅ Γ(Y, UY) := by
  haveI : IsIso (pushoutSection H hUST hUSX hUY) :=
    isIso_pushoutSection_of_isAffineOpen H hUST hUSX hUY hUS hUT hUX
  exact asIso (pushoutSection H hUST hUSX hUY)

/-- pushout の左の写像は、実際の構造層の引き戻し。 -/
@[reassoc]
theorem schemeAffinePullbackSectionIso_inl :
    pushout.inl _ _ ≫ (schemeAffinePullbackSectionIso H hUST hUSX hUY hUS hUT hUX).hom =
      g.appLE UX UY (by rw [hUY]; exact inf_le_left) := by
  simp only [schemeAffinePullbackSectionIso, asIso_hom, pushoutSection, pushout.inl_desc]

/-- pushout の右の写像も、実際の構造層の引き戻し。 -/
@[reassoc]
theorem schemeAffinePullbackSectionIso_inr :
    pushout.inr _ _ ≫ (schemeAffinePullbackSectionIso H hUST hUSX hUY hUS hUT hUX).hom =
      iY.appLE UT UY (by rw [hUY]; exact inf_le_right) := by
  simp only [schemeAffinePullbackSectionIso, asIso_hom, pushoutSection, pushout.inr_desc]

include H hUST hUSX hUY hUS hUT hUX in
/-- 同じ実際の底変換の交叉はアフィン開である。 -/
theorem schemeAffinePullbackIntersection_isAffineOpen : IsAffineOpen UY := by
  have : IsAffine US.toScheme := hUS
  have : IsAffine UT.toScheme := hUT
  have : IsAffine UX.toScheme := hUX
  exact IsAffine.of_isIso (Scheme.Hom.isPullback_resLE H hUST hUSX hUY).isoPullback.hom

end SerrePositivity.AlgebraicGeometry
