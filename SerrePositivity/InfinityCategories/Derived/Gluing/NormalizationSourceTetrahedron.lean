module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NormalizationAugmentationCoherence
public import SerrePositivity.InfinityCategories.Derived.Gluing.NormalizationProjectionFaceAgreement
public import SerrePositivity.InfinityCategories.Derived.Gluing.NormalizationStandardCompositionFaces
/-! # 正規化四面体の始側射影と二つの終側面の一致

概要：augmentation 四面体の始側射影を元 replacement 四面体へ戻し、二つの終側面を照合する。
方針：元宇宙へ戻す dg 関手の合成と、既存の全三角形の射影一致を用いる。
規約：選択済み四面体の三指定面を保持し、単位退化は仮定しない。
使われ方：左単位面の相対比較で Λ³₂ 上の二面を無条件に固定する。
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

lemma dgGluingNormalizationAugmentationTetrahedron_source_down :
    prismEndpoint 0 (Δ[3] ⊗ K) ≫ (dgGluingNormalizationAugmentationTetrahedron R E X Y f ≫
      dgNerve.map (dgUniverseLiftDown.{u, max u v, max u v} R E)) =
    dgGluingNormalizationCompositionTetrahedron R E X Y f ≫
      dgNerve.map (dgFunctorCommaReplacement R E E (DGFunctor.id E)) := by
  rw [← Category.assoc, dgGluingNormalizationAugmentationTetrahedron_source,
    Category.assoc, ← dgNerve.map_comp, dgGluingIdentityCommaSourceLift_down]

lemma dgGluingNormalizationSourceTetrahedron_one_eq_zero :
    (stdSimplex.δ (1 : Fin 4) ▷ K) ≫ prismEndpoint 0 (Δ[3] ⊗ K) ≫
      (dgGluingNormalizationAugmentationTetrahedron R E X Y f ≫
        dgNerve.map (dgUniverseLiftDown.{u, max u v, max u v} R E)) =
    (stdSimplex.δ (0 : Fin 4) ▷ K) ≫ prismEndpoint 0 (Δ[3] ⊗ K) ≫
      (dgGluingNormalizationAugmentationTetrahedron R E X Y f ≫
        dgNerve.map (dgUniverseLiftDown.{u, max u v, max u v} R E)) := by
  rw [dgGluingNormalizationAugmentationTetrahedron_source_down R E X Y f]
  rw [reassoc_of% dgGluingNormalizationCompositionTetrahedron_one R E X Y f,
    reassoc_of% dgGluingNormalizationCompositionTetrahedron_zero R E X Y f]
  exact dgGluingPostExitTriangle_replacement_eq R E X Y f
end SerrePositivity.InfinityCategories
