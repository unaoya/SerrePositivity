module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ExitUnitCollarTriangles
public import SerrePositivity.InfinityCategories.Derived.Gluing.NormalizationProjectionNaturality
/-! # 標準合成面と元の二つの Hom 鎖射影

概要：前側と終側の augmentation の射影面を、元 Hom 入力による同じ標準合成三角形へ同定する。
方針：Small 不要の coherent prism 自然性を実射影へ適用し、宇宙持ち上げを相殺する。
規約：閉射・全入力・標準合成三角形を選び直さない。
使われ方：単位補正の端を正本の左右係数合成三角形へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet MonoidalCategory
open scoped Simplicial
variable (R : Type u) [CommRing R] (E : Type (max u v)) [DGCategory R E]
  (X Y : DGFunctorCommaObject R E E (DGFunctor.id E))
  {K : SSet.{max u v}} (f : K ⟶ DGNerve.pinchedHom R
    (DGFunctorCommaObject R E E (DGFunctor.id E)) X Y)
local notation "Q" => DGFunctorCommaObject R E E (DGFunctor.id E)
lemma dgGluingPreAugmentationTriangle_target_standard :
    prismEndpoint 1 (Δ[2] ⊗ K) ≫
      (dgGluingPreNormalizeAugmentationTriangle R E X Y f ≫
        dgNerve.map (dgUniverseLiftDown.{u, max u v, max u v} R E)) =
      dgGluingDGCompositionTriangleFamily R E
        (SSet.const (X := K) (pinchedClosedVertex R E X.augmentation))
        (f ≫ pinchedHomChainMap ((dgFunctorCommaSource R E E (DGFunctor.id E)).map X Y)) := by
  have hn := dgGluingPreNormalizeProjectionInput_naturality R E X Y f
    (dgFunctorCommaSource R E E (DGFunctor.id E))
  change dgGluingSlicePrismTriangle (dgGluingIdentityCommaPreNormalizePrism R E X Y f) ≫
    dgNerve.map (dgFunctorCommaSource R E E (DGFunctor.id E)) = _ at hn
  rw [dgGluingIdentityCommaNormalizationClosedIn_source] at hn
  calc
    _ = dgGluingSlicePrismTriangle (dgGluingIdentityCommaPreNormalizePrism R E X Y f) ≫
        dgNerve.map (dgCommaAugmentationTargetLift R E E (DGFunctor.id E)) ≫
          dgNerve.map (dgUniverseLiftDown.{u, max u v, max u v} R E) := by
      rw [← Category.assoc, dgGluingPreNormalizeAugmentationTriangle_target_phase]
      simp only [Category.assoc]
    _ = _ := by
      rw [← dgNerve.map_comp, dgGluingIdentityCommaTargetLift_down]
      exact hn
lemma dgGluingExitAugmentationTriangle_source_standard :
    prismEndpoint 0 (Δ[2] ⊗ K) ≫
      (dgGluingExitAugmentationTriangle R E X Y f ≫
        dgNerve.map (dgUniverseLiftDown.{u, max u v, max u v} R E)) =
      dgGluingDGCompositionTriangleFamily R E
        (f ≫ pinchedHomChainMap ((dgFunctorCommaReplacement R E E (DGFunctor.id E)).map X Y))
        (SSet.const (X := K) (pinchedClosedVertex R E Y.augmentation)) := by
  have hn := dgGluingExitProjectionInput_naturality R E X Y f
    (dgFunctorCommaReplacement R E E (DGFunctor.id E))
  change dgGluingNormalizationExitTriangle R E X Y f ≫
    dgNerve.map (dgFunctorCommaReplacement R E E (DGFunctor.id E)) = _ at hn
  rw [dgGluingIdentityCommaNormalizationClosedOut_replacement] at hn
  calc
    _ = dgGluingNormalizationExitTriangle R E X Y f ≫
        dgNerve.map (dgCommaAugmentationSourceLift R E E (DGFunctor.id E)) ≫
          dgNerve.map (dgUniverseLiftDown.{u, max u v, max u v} R E) := by
      rw [← Category.assoc, dgGluingExitAugmentationTriangle_source_phase]
      simp only [Category.assoc]
    _ = _ := by
      rw [← dgNerve.map_comp, dgGluingIdentityCommaSourceLift_down]
      exact hn
end SerrePositivity.InfinityCategories
