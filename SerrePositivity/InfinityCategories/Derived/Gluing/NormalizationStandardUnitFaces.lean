module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ExitUnitCollarTriangles
public import SerrePositivity.InfinityCategories.Derived.Gluing.NormalizationProjectionNaturality
/-! # 標準合成面の恒等入力射影

概要：前側の replacement 面と終側の source 面を、閉恒等射を含む標準三角形へ同定する。
方針：Small 不要の coherent prism 自然性を実射影へ適用し、宇宙持ち上げを相殺する。
規約：閉射・全入力・標準合成三角形を選び直さない。
使われ方：D の単位則を接続する入口として、高次貼り合わせの残る単位面を保持する。
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
lemma dgGluingPreAugmentationTriangle_source_standard_unit_input :
    prismEndpoint 0 (Δ[2] ⊗ K) ≫
      (dgGluingPreNormalizeAugmentationTriangle R E X Y f ≫
        dgNerve.map (dgUniverseLiftDown.{u, max u v, max u v} R E)) =
      dgGluingDGCompositionTriangleFamily R E
        (SSet.const (X := K) (pinchedClosedVertex R E
          (𝟙 (ForgetEnrichment.of (Complex R) X.replacement))))
        (f ≫ pinchedHomChainMap ((dgFunctorCommaReplacement R E E (DGFunctor.id E)).map X Y)) := by
  have hn := dgGluingPreNormalizeProjectionInput_naturality R E X Y f
    (dgFunctorCommaReplacement R E E (DGFunctor.id E))
  change dgGluingSlicePrismTriangle (dgGluingIdentityCommaPreNormalizePrism R E X Y f) ≫
    dgNerve.map (dgFunctorCommaReplacement R E E (DGFunctor.id E)) = _ at hn
  rw [dgGluingIdentityCommaNormalizationClosedIn_replacement] at hn
  calc
    _ = dgGluingSlicePrismTriangle (dgGluingIdentityCommaPreNormalizePrism R E X Y f) ≫
        dgNerve.map (dgCommaAugmentationSourceLift R E E (DGFunctor.id E)) ≫
          dgNerve.map (dgUniverseLiftDown.{u, max u v, max u v} R E) := by
      rw [dgGluingPreNormalizeAugmentationTriangle, ← Category.assoc,
        ← Category.assoc, prismEndpoint_naturality]
      simp only [Category.assoc]
      erw [reassoc_of% (dgGluingCommaAugmentationPrism_zero R E E (DGFunctor.id E))]
    _ = _ := by
      rw [← dgNerve.map_comp, dgGluingIdentityCommaSourceLift_down]
      exact hn
lemma dgGluingExitAugmentationTriangle_target_standard_unit_input :
    prismEndpoint 1 (Δ[2] ⊗ K) ≫
      (dgGluingExitAugmentationTriangle R E X Y f ≫
        dgNerve.map (dgUniverseLiftDown.{u, max u v, max u v} R E)) =
      dgGluingDGCompositionTriangleFamily R E
        (f ≫ pinchedHomChainMap ((dgFunctorCommaSource R E E (DGFunctor.id E)).map X Y))
        (SSet.const (X := K) (pinchedClosedVertex R E
          (𝟙 (ForgetEnrichment.of (Complex R) Y.source)))) := by
  have hn := dgGluingExitProjectionInput_naturality R E X Y f
    (dgFunctorCommaSource R E E (DGFunctor.id E))
  change dgGluingNormalizationExitTriangle R E X Y f ≫
    dgNerve.map (dgFunctorCommaSource R E E (DGFunctor.id E)) = _ at hn
  rw [dgGluingIdentityCommaNormalizationClosedOut_source] at hn
  calc
    _ = dgGluingNormalizationExitTriangle R E X Y f ≫
        dgNerve.map (dgCommaAugmentationTargetLift R E E (DGFunctor.id E)) ≫
          dgNerve.map (dgUniverseLiftDown.{u, max u v, max u v} R E) := by
      rw [dgGluingExitAugmentationTriangle, ← Category.assoc,
        ← Category.assoc, prismEndpoint_naturality]
      simp only [Category.assoc]
      erw [reassoc_of% (dgGluingCommaAugmentationPrism_one R E E (DGFunctor.id E))]
    _ = _ := by
      rw [← dgNerve.map_comp, dgGluingIdentityCommaTargetLift_down]
      exact hn
end SerrePositivity.InfinityCategories
