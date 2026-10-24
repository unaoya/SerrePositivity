module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NormalizationSourceTetrahedron
public import SerrePositivity.InfinityCategories.Derived.Gluing.NormalizationStandardUnitFaces
public import SerrePositivity.InfinityCategories.Derived.Gluing.DGCompositionFirstUnitTriangle
/-!
概要：正規化 augmentation 四面体の始側射影の第三面を厳密な単位退化へ同定する。
方針：標準第一単位三角形を元の終側三角形の始辺と照合する。
規約：Small 仮定なしで同じ四面体・同じ全入力を保持する。
使われ方：Λ³₂ の相対比較に必要な最後の固定面を供給する。
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

lemma dgGluingNormalizationSourceTetrahedron_unit_face :
    (stdSimplex.δ (3 : Fin 4) ▷ K) ≫ prismEndpoint 0 (Δ[3] ⊗ K) ≫
      (dgGluingNormalizationAugmentationTetrahedron R E X Y f ≫
        dgNerve.map (dgUniverseLiftDown.{u, max u v, max u v} R E)) =
    (stdSimplex.σ (0 : Fin 2) ▷ K) ≫ (stdSimplex.δ (2 : Fin 3) ▷ K) ≫
      (stdSimplex.δ (0 : Fin 4) ▷ K) ≫ prismEndpoint 0 (Δ[3] ⊗ K) ≫
        (dgGluingNormalizationAugmentationTetrahedron R E X Y f ≫
          dgNerve.map (dgUniverseLiftDown.{u, max u v, max u v} R E)) := by
  have hpre : (stdSimplex.δ (3 : Fin 4) ▷ K) ≫ prismEndpoint 0 (Δ[3] ⊗ K) ≫
      (dgGluingNormalizationAugmentationTetrahedron R E X Y f ≫
        dgNerve.map (dgUniverseLiftDown.{u, max u v, max u v} R E)) =
      prismEndpoint 0 (Δ[2] ⊗ K) ≫
        (dgGluingPreNormalizeAugmentationTriangle R E X Y f ≫
          dgNerve.map (dgUniverseLiftDown.{u, max u v, max u v} R E)) := by
    rw [← reassoc_of% prismEndpoint_naturality,
      reassoc_of% dgGluingNormalizationAugmentationTetrahedron_three R E X Y f]
  have hexit : (stdSimplex.δ (0 : Fin 4) ▷ K) ≫ prismEndpoint 0 (Δ[3] ⊗ K) ≫
      (dgGluingNormalizationAugmentationTetrahedron R E X Y f ≫
        dgNerve.map (dgUniverseLiftDown.{u, max u v, max u v} R E)) =
      prismEndpoint 0 (Δ[2] ⊗ K) ≫
        (dgGluingExitAugmentationTriangle R E X Y f ≫
          dgNerve.map (dgUniverseLiftDown.{u, max u v, max u v} R E)) := by
    rw [← reassoc_of% prismEndpoint_naturality,
      reassoc_of% dgGluingNormalizationAugmentationTetrahedron_zero R E X Y f]
    rfl
  rw [hpre, hexit, dgGluingPreAugmentationTriangle_source_standard_unit_input,
    dgGluingExitAugmentationTriangle_source_standard,
    dgGluingDGCompositionTriangleFamily_first_unit,
    dgGluingDGCompositionTriangleFamily_two]
  rfl
end SerrePositivity.InfinityCategories
