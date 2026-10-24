module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NormalizationProjectionInputs

/-! # 標準合成四面体の augmentation 整合性

概要：同じ四面体の二射影を結ぶ実ホモトピーと、三つの標準合成面を保持する。
方針：元 augmentation を四面体全体へ適用し、区間因子を転置する。
規約：指定三面と元 Hom 入力を保ち、射影自然性だけは別の明示入力とする。
使われ方：側面を含む相対二次元比較を選択済み二変形へ移すための高次データ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded MonoidalCategory DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E]
  (X Y : DGFunctorCommaObject R E E (DGFunctor.id E))
  {K : SSet.{max u v}} (f : K ⟶ DGNerve.pinchedHom R
    (DGFunctorCommaObject R E E (DGFunctor.id E)) X Y)

/-- 概要：正規化の実四面体上で元 augmentation 全体を評価する。
方針：全区間と四面体を保持して後合成する。
規約：四面体の新しい充填は選ばない。使われ方：二射影間の三面付きホモトピー。 -/
def dgGluingNormalizationAugmentationTetrahedron :=
  (Δ[1] ◁ dgGluingNormalizationCompositionTetrahedron R E X Y f) ≫
    dgGluingCommaAugmentationPrism R E E (DGFunctor.id E)

lemma dgGluingNormalizationAugmentationTetrahedron_source :
    prismEndpoint 0 (Δ[3] ⊗ K) ≫ dgGluingNormalizationAugmentationTetrahedron R E X Y f =
      dgGluingNormalizationCompositionTetrahedron R E X Y f ≫
        dgNerve.map (dgCommaAugmentationSourceLift R E E (DGFunctor.id E)) := by
  rw [dgGluingNormalizationAugmentationTetrahedron, ← Category.assoc,
    prismEndpoint_naturality, Category.assoc, dgGluingCommaAugmentationPrism_zero]

lemma dgGluingNormalizationAugmentationTetrahedron_target :
    prismEndpoint 1 (Δ[3] ⊗ K) ≫ dgGluingNormalizationAugmentationTetrahedron R E X Y f =
      dgGluingNormalizationCompositionTetrahedron R E X Y f ≫
        dgNerve.map (dgCommaAugmentationTargetLift R E E (DGFunctor.id E)) := by
  rw [dgGluingNormalizationAugmentationTetrahedron, ← Category.assoc,
    prismEndpoint_naturality, Category.assoc, dgGluingCommaAugmentationPrism_one]

lemma dgGluingNormalizationAugmentationTetrahedron_zero :
    (Δ[1] ◁ (stdSimplex.δ (0 : Fin 4) ▷ K)) ≫
        dgGluingNormalizationAugmentationTetrahedron R E X Y f =
      (Δ[1] ◁ dgGluingNormalizationExitTriangle R E X Y f) ≫
        dgGluingCommaAugmentationPrism R E E (DGFunctor.id E) := by
  rw [dgGluingNormalizationAugmentationTetrahedron, ← Category.assoc, ← whiskerLeft_comp,
    dgGluingNormalizationCompositionTetrahedron_zero]

lemma dgGluingNormalizationAugmentationTetrahedron_one :
    (Δ[1] ◁ (stdSimplex.δ (1 : Fin 4) ▷ K)) ≫
        dgGluingNormalizationAugmentationTetrahedron R E X Y f =
      dgGluingPostNormalizeAugmentationTriangle R E X Y f := by
  rw [dgGluingNormalizationAugmentationTetrahedron, ← Category.assoc, ← whiskerLeft_comp,
    dgGluingNormalizationCompositionTetrahedron_one]
  rfl

lemma dgGluingNormalizationAugmentationTetrahedron_two :
    (Δ[1] ◁ (stdSimplex.δ (2 : Fin 4) ▷ K)) ≫
        dgGluingNormalizationAugmentationTetrahedron R E X Y f =
      (Δ[1] ◁ dgGluingNormalizationEntranceTriangle R E X Y f) ≫
        dgGluingCommaAugmentationPrism R E E (DGFunctor.id E) := by
  rw [dgGluingNormalizationAugmentationTetrahedron, ← Category.assoc, ← whiskerLeft_comp]
  rfl

lemma dgGluingNormalizationAugmentationTetrahedron_three :
    (Δ[1] ◁ (stdSimplex.δ (3 : Fin 4) ▷ K)) ≫
        dgGluingNormalizationAugmentationTetrahedron R E X Y f =
      dgGluingPreNormalizeAugmentationTriangle R E X Y f := by
  rw [dgGluingNormalizationAugmentationTetrahedron, ← Category.assoc, ← whiskerLeft_comp,
    dgGluingNormalizationCompositionTetrahedron_three]
  rfl

/-- 概要：同じ実四面体の二射影間のホモトピー。
方針：augmentation の区間因子だけを後ろへ転置する。
規約：二端は同じ四面体の射影そのもの。使われ方：選択済み変形への相対比較。 -/
def dgGluingNormalizationAugmentationTetrahedronHomotopy : SSet.Homotopy
    (dgGluingNormalizationCompositionTetrahedron R E X Y f ≫
      dgNerve.map (dgCommaAugmentationSourceLift R E E (DGFunctor.id E)))
    (dgGluingNormalizationCompositionTetrahedron R E X Y f ≫
      dgNerve.map (dgCommaAugmentationTargetLift R E E (DGFunctor.id E))) where
  h := (β_ (Δ[3] ⊗ K) (Δ[1] : SSet.{max u v})).hom ≫
    dgGluingNormalizationAugmentationTetrahedron R E X Y f
  h₀ := by
    have hi : (ι₀ : Δ[3] ⊗ K ⟶ _) ≫
        (β_ (Δ[3] ⊗ K) (Δ[1] : SSet.{max u v})).hom = prismEndpoint 0 (Δ[3] ⊗ K) := rfl
    rw [← Category.assoc, hi, dgGluingNormalizationAugmentationTetrahedron_source]
    rfl
  h₁ := by
    have hi : (ι₁ : Δ[3] ⊗ K ⟶ _) ≫
        (β_ (Δ[3] ⊗ K) (Δ[1] : SSet.{max u v})).hom = prismEndpoint 1 (Δ[3] ⊗ K) := rfl
    rw [← Category.assoc, hi, dgGluingNormalizationAugmentationTetrahedron_target]
    rfl
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

end SerrePositivity.InfinityCategories
