module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NormalizationSourceTetrahedron
public import SerrePositivity.InfinityCategories.Derived.Gluing.NormalizationStandardUnitFaces
public import SerrePositivity.InfinityCategories.Derived.Gluing.DGCompositionSecondUnitTriangle
/-!
概要：正規化 augmentation 四面体の終側射影の第一面を厳密な単位退化へ同定する。
方針：同じ後正規化三角形の射影自然性へ coherent 第二単位則を代入する。
規約：Small 仮定なしで同じ四面体と全 Hom 入力を保持する。
使われ方：主経路の右単位閉路を同じ全正方形の退化として消去する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded MonoidalCategory DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (E : Type (max u v)) [DGCategory R E]
  (X Y : DGFunctorCommaObject R E E (DGFunctor.id E)) {K : SSet.{max u v}}
  (f : K ⟶ DGNerve.pinchedHom R (DGFunctorCommaObject R E E (DGFunctor.id E)) X Y)

lemma dgGluingPostAugmentationTriangle_target_unit_face :
    prismEndpoint 1 (Δ[2] ⊗ K) ≫
      (dgGluingPostNormalizeAugmentationTriangle R E X Y f ≫
        dgNerve.map (dgUniverseLiftDown.{u, max u v, max u v} R E)) =
    (stdSimplex.σ (1 : Fin 2) ▷ K) ≫ (stdSimplex.δ (2 : Fin 3) ▷ K) ≫
      prismEndpoint 1 (Δ[2] ⊗ K) ≫
        (dgGluingPostNormalizeAugmentationTriangle R E X Y f ≫
          dgNerve.map (dgUniverseLiftDown.{u, max u v, max u v} R E)) := by
  have hn := dgGluingPostNormalizeProjectionInput_naturality R E X Y f
    (dgFunctorCommaSource R E E (DGFunctor.id E))
  change dgGluingSlicePrismTriangle (dgGluingIdentityCommaPostNormalizePrism R E X Y f) ≫
    dgNerve.map (dgFunctorCommaSource R E E (DGFunctor.id E)) = _ at hn
  rw [dgGluingIdentityCommaNormalizationClosedOut_source] at hn
  have hp : prismEndpoint 1 (Δ[2] ⊗ K) ≫
      (dgGluingPostNormalizeAugmentationTriangle R E X Y f ≫
        dgNerve.map (dgUniverseLiftDown.{u, max u v, max u v} R E)) =
      dgGluingSlicePrismTriangle (dgGluingIdentityCommaPostNormalizePrism R E X Y f) ≫
        dgNerve.map (dgFunctorCommaSource R E E (DGFunctor.id E)) := by
    rw [dgGluingPostNormalizeAugmentationTriangle, ← Category.assoc,
      ← Category.assoc, prismEndpoint_naturality]
    simp only [Category.assoc]
    erw [reassoc_of% (dgGluingCommaAugmentationPrism_one R E E (DGFunctor.id E))]
    rw [← dgNerve.map_comp, dgGluingIdentityCommaTargetLift_down]
  rw [hp, hn, dgGluingDGCompositionTriangleFamily_two]
  exact dgGluingDGCompositionTriangleFamily_second_unit R E _

lemma dgGluingNormalizationTargetTetrahedron_unit_face :
    (stdSimplex.δ (1 : Fin 4) ▷ K) ≫ prismEndpoint 1 (Δ[3] ⊗ K) ≫
      (dgGluingNormalizationAugmentationTetrahedron R E X Y f ≫
        dgNerve.map (dgUniverseLiftDown.{u, max u v, max u v} R E)) =
    (stdSimplex.σ (1 : Fin 2) ▷ K) ≫ (stdSimplex.δ (2 : Fin 3) ▷ K) ≫
      (stdSimplex.δ (1 : Fin 4) ▷ K) ≫ prismEndpoint 1 (Δ[3] ⊗ K) ≫
        (dgGluingNormalizationAugmentationTetrahedron R E X Y f ≫
          dgNerve.map (dgUniverseLiftDown.{u, max u v, max u v} R E)) := by
  have hp : (stdSimplex.δ (1 : Fin 4) ▷ K) ≫ prismEndpoint 1 (Δ[3] ⊗ K) ≫
      (dgGluingNormalizationAugmentationTetrahedron R E X Y f ≫
        dgNerve.map (dgUniverseLiftDown.{u, max u v, max u v} R E)) =
      prismEndpoint 1 (Δ[2] ⊗ K) ≫
        (dgGluingPostNormalizeAugmentationTriangle R E X Y f ≫
          dgNerve.map (dgUniverseLiftDown.{u, max u v, max u v} R E)) := by
    rw [← reassoc_of% prismEndpoint_naturality,
      reassoc_of% dgGluingNormalizationAugmentationTetrahedron_one R E X Y f]
  rw [hp]
  exact dgGluingPostAugmentationTriangle_target_unit_face R E X Y f
end SerrePositivity.InfinityCategories
