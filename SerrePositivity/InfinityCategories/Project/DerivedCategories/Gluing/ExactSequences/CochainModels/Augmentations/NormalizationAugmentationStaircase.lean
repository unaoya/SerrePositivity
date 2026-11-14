module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.CochainModels.Augmentations.NormalizationAugmentationCoherence

/-! # augmentation 四面体の四つの高次貼り合わせ片

概要：四面体全体の augmentation を四つの四単体族に分け、共有三面を保持する。
方針：Mathlib の標準単体と区間の積の非退化単体を使う。
規約：充填を選び直さず、同じ全 augmentation へ制限する。
使われ方：側面の補正も含めた相対二次元比較の高次整合性を取り出す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory DifferentialGraded SSet
open scoped _root_.Simplicial

def dgGluingNormalizationStaircaseSimplex (i : Fin 4) :
    (Δ[4] : SSet.{u}) ⟶ Δ[3] ⊗ Δ[1] :=
  SSet.yonedaEquiv.symm (prodStdSimplex₁.nonDegenerateEquiv i).val

lemma dgGluingNormalizationStaircaseSimplex_shared (i : Fin 3) :
    stdSimplex.δ i.castSucc.succ ≫ dgGluingNormalizationStaircaseSimplex.{u} i.castSucc =
      stdSimplex.δ i.succ.castSucc ≫ dgGluingNormalizationStaircaseSimplex i.succ := by
  apply SSet.yonedaEquiv.injective
  rw [stdSimplex.yonedaEquiv_δ_comp, stdSimplex.yonedaEquiv_δ_comp]
  simp only [dgGluingNormalizationStaircaseSimplex, Equiv.apply_symm_apply]
  rw [prodStdSimplex₁.δ_succ_nonDegenerateEquiv,
    prodStdSimplex₁.δ_castSucc_nonDegenerateEquiv, Fin.succ_castSucc]

lemma dgGluingNormalizationStaircaseSimplex_target :
    stdSimplex.δ (0 : Fin 5) ≫ dgGluingNormalizationStaircaseSimplex.{u} 0 = ι₁ := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext <;> apply SSet.stdSimplex.ext <;> intro j <;> fin_cases j <;> rfl

lemma dgGluingNormalizationStaircaseSimplex_source :
    stdSimplex.δ (4 : Fin 5) ≫ dgGluingNormalizationStaircaseSimplex.{u} 3 = ι₀ := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext <;> apply SSet.stdSimplex.ext <;> intro j <;> fin_cases j <;> rfl

variable (R : Type u) [CommRing R] (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R E E (DGFunctor.id E))
  {K : SSet.{max u v}} (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R E E (DGFunctor.id E)) X Y)

def dgGluingNormalizationAugmentationStaircase (i : Fin 4) :=
  (dgGluingNormalizationStaircaseSimplex i ▷ K) ≫
    ((β_ (Δ[3] : SSet.{max u v}) Δ[1]).hom ▷ K) ≫
      (α_ (Δ[1] : SSet.{max u v}) Δ[3] K).hom ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNormalizationAugmentationTetrahedron R E X Y f

lemma dgGluingNormalizationAugmentationStaircase_shared (i : Fin 3) :
    (stdSimplex.δ i.castSucc.succ ▷ K) ≫
        dgGluingNormalizationAugmentationStaircase R E X Y f i.castSucc =
      (stdSimplex.δ i.succ.castSucc ▷ K) ≫
        dgGluingNormalizationAugmentationStaircase R E X Y f i.succ := by
  simp only [dgGluingNormalizationAugmentationStaircase, ← Category.assoc,
    ← comp_whiskerRight, dgGluingNormalizationStaircaseSimplex_shared]

lemma dgGluingNormalizationAugmentationStaircase_target :
    (stdSimplex.δ (0 : Fin 5) ▷ K) ≫
        dgGluingNormalizationAugmentationStaircase R E X Y f 0 =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNormalizationCompositionTetrahedron R E X Y f ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationTargetLift R E E (DGFunctor.id E)) := by
  calc
    _ = (ι₁ ▷ K) ≫ ((β_ (Δ[3] : SSet.{max u v}) Δ[1]).hom ▷ K) ≫
        (α_ (Δ[1] : SSet.{max u v}) Δ[3] K).hom ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNormalizationAugmentationTetrahedron R E X Y f := by
      simp only [dgGluingNormalizationAugmentationStaircase, ← Category.assoc,
        ← comp_whiskerRight, dgGluingNormalizationStaircaseSimplex_target]
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[3] ⊗ K) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNormalizationAugmentationTetrahedron R E X Y f := rfl
    _ = _ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNormalizationAugmentationTetrahedron_target R E X Y f

lemma dgGluingNormalizationAugmentationStaircase_source :
    (stdSimplex.δ (4 : Fin 5) ▷ K) ≫
        dgGluingNormalizationAugmentationStaircase R E X Y f 3 =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNormalizationCompositionTetrahedron R E X Y f ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSourceLift R E E (DGFunctor.id E)) := by
  calc
    _ = (ι₀ ▷ K) ≫ ((β_ (Δ[3] : SSet.{max u v}) Δ[1]).hom ▷ K) ≫
        (α_ (Δ[1] : SSet.{max u v}) Δ[3] K).hom ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNormalizationAugmentationTetrahedron R E X Y f := by
      simp only [dgGluingNormalizationAugmentationStaircase, ← Category.assoc,
        ← comp_whiskerRight, dgGluingNormalizationStaircaseSimplex_source]
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[3] ⊗ K) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNormalizationAugmentationTetrahedron R E X Y f := rfl
    _ = _ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNormalizationAugmentationTetrahedron_source R E X Y f

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
