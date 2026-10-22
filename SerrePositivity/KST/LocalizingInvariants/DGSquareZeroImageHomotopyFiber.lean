module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroImagePullback
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackComparisonQuasiIso

/-!
概要：係数像の平方零代数から、元の係数商と零切断の実経路模型への準同型比較。
方針：元の実 pullback の同型と、次数全射な係数商の比較定理を合成する。
規約：包含と底射影の二脚を保持。使われ方：実乗法的経路からの像への導来 lift。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZeroImageFiber
variable {R : Type u} [CommRing R] {A : Mon (Complex R)} {M N : Bimod A A} (f : M ⟶ N)

lemma quotient_epi : Epi (quotient f).hom := by
  have := DGBimoduleCokernel.projection_epi f
  change Epi (biprod.map (𝟙 A.X) (DGBimoduleCokernel.projection f).hom)
  infer_instance

def strictIso : SquareZero.algebra A (DGBimoduleImage.obj f) ≅
    MonoidPullback.obj (quotient f) (zeroSection f) :=
  (isLimit f).conePointUniqueUpToIso (MonoidPullback.isLimit _ _)

lemma strictIso_inclusion : (strictIso f).hom ≫ MonoidPullback.fst (quotient f) (zeroSection f) =
    inclusion f := (isLimit f).conePointUniqueUpToIso_hom_comp
      (MonoidPullback.isLimit _ _) WalkingCospan.left

lemma strictIso_projection : (strictIso f).hom ≫ MonoidPullback.snd (quotient f) (zeroSection f) =
    projection f := (isLimit f).conePointUniqueUpToIso_hom_comp
      (MonoidPullback.isLimit _ _) WalkingCospan.right

abbrev model := DGAlgebra.HomotopyPullbackModel.algebra R (quotient f) (zeroSection f)

def comparison : SquareZero.algebra A (DGBimoduleImage.obj f) ⟶ model f :=
  (strictIso f).hom ≫ DGAlgebra.HomotopyPullbackModel.comparison R _ _

lemma comparison_quasiIso : QuasiIso (comparison f).hom := by
  have := quotient_epi f
  change QuasiIso ((strictIso f).hom.hom ≫ (DGAlgebra.HomotopyPullbackModel.comparison R _ _).hom)
  exact quasiIso_comp _ _ (hφ := quasiIso_of_isIso ((Mon.forget (Complex R)).mapIso
    (strictIso f)).hom) (hφ' := DGAlgebra.HomotopyPullbackModel.comparison_quasiIso_left R _ _)

lemma comparison_left : comparison f ≫ DGAlgebra.HomotopyPullbackModel.left R _ _ =
    inclusion f := by
  rw [comparison, Category.assoc, DGAlgebra.HomotopyPullbackModel.comparison_left,
    strictIso_inclusion]

lemma comparison_right : comparison f ≫ DGAlgebra.HomotopyPullbackModel.right R _ _ =
    projection f := by
  rw [comparison, Category.assoc, DGAlgebra.HomotopyPullbackModel.comparison_right,
    strictIso_projection]

end SerrePositivity.KST.LocalizingInvariants.SquareZeroImageFiber
