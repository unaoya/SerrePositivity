module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroImageHomotopyFiber
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackComparisonQuasiIso

/-!
概要：零切断を第一脚に置き、係数像の平方零代数から実経路模型へ準同型比較。
方針：元の実 pullback 錐の flip と、第二脚の全射性による比較定理を合成する。
規約：包含と底射影の二脚を保持。使われ方：実乗法的経路からの像への導来 lift。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZeroImageFiber.ZeroStart
variable {R : Type u} [CommRing R] {A : Mon (Complex R)} {M N : Bimod A A} (f : M ⟶ N)

def isLimit : IsLimit (SquareZeroImageFiber.cone f).flip :=
  PullbackCone.flipIsLimit (SquareZeroImageFiber.isLimit f)

def strictIso : SquareZero.algebra A (DGBimoduleImage.obj f) ≅
    MonoidPullback.obj (zeroSection f) (quotient f) :=
  (isLimit f).conePointUniqueUpToIso (MonoidPullback.isLimit _ _)

lemma strictIso_left : (strictIso f).hom ≫ MonoidPullback.fst (zeroSection f) (quotient f) =
    projection f := (isLimit f).conePointUniqueUpToIso_hom_comp
      (MonoidPullback.isLimit _ _) WalkingCospan.left

lemma strictIso_right : (strictIso f).hom ≫ MonoidPullback.snd (zeroSection f) (quotient f) =
    inclusion f := (isLimit f).conePointUniqueUpToIso_hom_comp
      (MonoidPullback.isLimit _ _) WalkingCospan.right

abbrev model := DGAlgebra.HomotopyPullbackModel.algebra R (zeroSection f) (quotient f)

def comparison : SquareZero.algebra A (DGBimoduleImage.obj f) ⟶ model f :=
  (strictIso f).hom ≫ DGAlgebra.HomotopyPullbackModel.comparison R _ _

lemma comparison_quasiIso : QuasiIso (comparison f).hom := by
  have := quotient_epi f
  change QuasiIso ((strictIso f).hom.hom ≫ (DGAlgebra.HomotopyPullbackModel.comparison R _ _).hom)
  exact quasiIso_comp _ _ (hφ := quasiIso_of_isIso ((Mon.forget (Complex R)).mapIso
    (strictIso f)).hom) (hφ' := DGAlgebra.HomotopyPullbackModel.comparison_quasiIso_right R _ _)

lemma comparison_left : comparison f ≫ DGAlgebra.HomotopyPullbackModel.left R _ _ =
    projection f := by
  rw [comparison, Category.assoc, DGAlgebra.HomotopyPullbackModel.comparison_left,
    strictIso_left]

lemma comparison_right : comparison f ≫ DGAlgebra.HomotopyPullbackModel.right R _ _ =
    inclusion f := by
  rw [comparison, Category.assoc, DGAlgebra.HomotopyPullbackModel.comparison_right,
    strictIso_right]

end SerrePositivity.KST.LocalizingInvariants.SquareZeroImageFiber.ZeroStart
