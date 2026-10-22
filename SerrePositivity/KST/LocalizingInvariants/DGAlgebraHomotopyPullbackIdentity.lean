module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackComparisonQuasiIso

/-!
概要：左脚が元の恒等射の経路模型では、元の右射影が準同型であることを示す。
方針：元の通常 pullback の右射影の同型性と、経路模型への元の準同型比較を使う。
規約：経路の反転や乗法的対称性を仮定しない。使われ方：実 cospan の pro 底変更。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
variable (R : Type u) [CommRing R] {B C : Mon (Complex R)} (g : C ⟶ B)

lemma right_identity_quasiIso : QuasiIso (right R (𝟙 B) g).hom := by
  have : IsIso (MonoidPullback.snd (𝟙 B) g).hom := by
    change IsIso (pullback.snd (𝟙 B.X) g.hom)
    infer_instance
  have : QuasiIso ((comparison R (𝟙 B) g).hom ≫ (right R (𝟙 B) g).hom) := by
    change QuasiIso ((comparison R (𝟙 B) g ≫ right R (𝟙 B) g).hom)
    rw [comparison_right]
    exact quasiIso_of_isIso _
  have := comparison_quasiIso_left R (𝟙 B) g
  exact quasiIso_of_comp_left (comparison R (𝟙 B) g).hom (right R (𝟙 B) g).hom

lemma identity_isConnective (hC : IsConnective R C) : IsConnective R (algebra R (𝟙 B) g) := by
  have := right_identity_quasiIso R g
  have : C.X.IsLE 0 := hC
  apply (CochainComplex.isLE_iff _ 0).2
  intro i hi
  exact (exactAt_iff_of_quasiIsoAt (right R (𝟙 B) g).hom i).2
    (CochainComplex.exactAt_of_isLE C.X 0 i hi)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
