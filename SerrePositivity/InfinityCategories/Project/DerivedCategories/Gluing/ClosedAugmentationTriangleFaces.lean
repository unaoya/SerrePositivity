module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ClosedAugmentationTriangleComponents
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCommaAugPrismComponent

/-! # 閉 augmentation 側面の指定三辺

概要：側面の二つの生成三角形から、元閉射の二射影・両端 augmentation・対角を回収する。
方針：実 prism の単体的自然性を六つの面へ適用する。
規約：三角形を選び直さず、固定相と定値入力も実一単体として照合する。
使われ方：標準正規化側面を単位退化三角形へ同定する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]

lemma dgGluingSimplexConstantEdgePullback {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R E n) (i : Fin (n + 1)) :
    s.pullback (OrderHom.const (Fin 2) i) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ofEdge (fun _ : Fin 2 => s.obj i) (unitElement R (s.obj i)) := by
  have hc : (s.pullback (OrderHom.const (Fin 2) i)).edgeCycle 0 1 (by decide) =
      _root_.SerrePositivity.DifferentialGraded.unitElement R (s.obj i) := by
    apply Subtype.ext
    apply eq_of_heq
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_collapsed_pair s.toSimplexData
      (OrderHom.const (Fin 2) i) {0, 1} 0 1 0
      (by decide) (by decide) (by decide) (by decide)
      (by
        intro h
        have hh : (0 : Fin 2) = 1 := h (by decide) (by decide) rfl
        exact (by decide : (0 : Fin 2) ≠ 1) hh)
      (by decide)
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ofEdge_edgeCycle (s.pullback (OrderHom.const (Fin 2) i)), hc]
  rfl
lemma dgGluingIdentityCommaAugmentationUnitEdge_eq
    (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R E E (DGFunctor.id E)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismSimplex R E E (DGFunctor.id E)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ofEdge (fun _ : Fin 2 => X) (unitElement R X)) OrderHom.id =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R E X.augmentation).edge := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.edgeEquiv.injective
  refine Sigma.ext ?_ ?_
  · funext i
    fin_cases i <;> rfl
  · apply heq_of_eq
    apply Subtype.ext
    exact eq_of_heq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismSimplex_unitEdge R E E (DGFunctor.id E) X)


variable (A B : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R E E (DGFunctor.id E))
  (k : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) A ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) B)
local notation "Q" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R E E (DGFunctor.id E)

lemma dgGluingClosedAugmentationTriangle_diagonal (i : Fin 2) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingClosedAugmentationTriangle R E A B k i).pullback
      (SimplexCategory.δ (1 : Fin 3)).toOrderHom =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismSimplex R E E (DGFunctor.id E)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R Q k).edge OrderHom.id := by
  have h0 : (SimplexCategory.σ (0 : Fin 2)).toOrderHom.comp
      (SimplexCategory.δ (1 : Fin 3)).toOrderHom = OrderHom.id := by
    ext j
    fin_cases j <;> rfl
  have h1 : (SimplexCategory.σ (1 : Fin 2)).toOrderHom.comp
      (SimplexCategory.δ (1 : Fin 3)).toOrderHom = OrderHom.id := by
    ext j
    fin_cases j <;> rfl
  fin_cases i <;> dsimp [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingClosedAugmentationTriangle]
  all_goals rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismSimplex_pullback,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_comp, h0, h1, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_id]
private lemma dgGluingClosedPrismPhaseZero {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R Q n) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismSimplex R E E (DGFunctor.id E) s (OrderHom.const _ 0) =
      s.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSource R E E (DGFunctor.id E)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData_zero R E E (DGFunctor.id E) s.toSimplexData
private lemma dgGluingClosedPrismPhaseOne {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R Q n) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismSimplex R E E (DGFunctor.id E) s (OrderHom.const _ 1) =
      s.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationTarget R E E (DGFunctor.id E)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData_one R E E (DGFunctor.id E) s.toSimplexData

lemma dgGluingClosedAugmentationTriangle_zero_first :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingClosedAugmentationTriangle R E A B k 0).pullback
      (SimplexCategory.δ (2 : Fin 3)).toOrderHom =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R Q k).edge.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSource R E E (DGFunctor.id E)) := by
  have hτ : (SimplexCategory.σ (1 : Fin 2)).toOrderHom.comp
      (SimplexCategory.δ (2 : Fin 3)).toOrderHom = OrderHom.id := by
    ext j
    fin_cases j <;> rfl
  have hβ : (SimplexCategory.σ (0 : Fin 2)).toOrderHom.comp
      (SimplexCategory.δ (2 : Fin 3)).toOrderHom = OrderHom.const _ 0 := by
    ext j
    fin_cases j <;> rfl
  dsimp [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingClosedAugmentationTriangle]
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismSimplex_pullback, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_comp,
    hτ, hβ, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_id, dgGluingClosedPrismPhaseZero]
lemma dgGluingClosedAugmentationTriangle_one_last :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingClosedAugmentationTriangle R E A B k 1).pullback
      (SimplexCategory.δ (0 : Fin 3)).toOrderHom =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R Q k).edge.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationTarget R E E (DGFunctor.id E)) := by
  have hτ : (SimplexCategory.σ (0 : Fin 2)).toOrderHom.comp
      (SimplexCategory.δ (0 : Fin 3)).toOrderHom = OrderHom.id := by
    ext j
    fin_cases j <;> rfl
  have hβ : (SimplexCategory.σ (1 : Fin 2)).toOrderHom.comp
      (SimplexCategory.δ (0 : Fin 3)).toOrderHom = OrderHom.const _ 1 := by
    ext j
    fin_cases j <;> rfl
  dsimp [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingClosedAugmentationTriangle]
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismSimplex_pullback, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_comp,
    hτ, hβ, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_id, dgGluingClosedPrismPhaseOne]
lemma dgGluingClosedAugmentationTriangle_zero_last :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingClosedAugmentationTriangle R E A B k 0).pullback
      (SimplexCategory.δ (0 : Fin 3)).toOrderHom =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R E B.augmentation).edge := by
  have hτ : (SimplexCategory.σ (1 : Fin 2)).toOrderHom.comp
      (SimplexCategory.δ (0 : Fin 3)).toOrderHom = OrderHom.const _ 1 := by
    ext j
    fin_cases j <;> rfl
  have hβ : (SimplexCategory.σ (0 : Fin 2)).toOrderHom.comp
      (SimplexCategory.δ (0 : Fin 3)).toOrderHom = OrderHom.id := by
    ext j
    fin_cases j <;> rfl
  dsimp [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingClosedAugmentationTriangle]
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismSimplex_pullback, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_comp, hτ, hβ,
    dgGluingSimplexConstantEdgePullback]
  exact dgGluingIdentityCommaAugmentationUnitEdge_eq R E B
lemma dgGluingClosedAugmentationTriangle_one_first :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingClosedAugmentationTriangle R E A B k 1).pullback
      (SimplexCategory.δ (2 : Fin 3)).toOrderHom =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R E A.augmentation).edge := by
  have hτ : (SimplexCategory.σ (0 : Fin 2)).toOrderHom.comp
      (SimplexCategory.δ (2 : Fin 3)).toOrderHom = OrderHom.const _ 0 := by
    ext j
    fin_cases j <;> rfl
  have hβ : (SimplexCategory.σ (1 : Fin 2)).toOrderHom.comp
      (SimplexCategory.δ (2 : Fin 3)).toOrderHom = OrderHom.id := by
    ext j
    fin_cases j <;> rfl
  dsimp [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingClosedAugmentationTriangle]
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismSimplex_pullback, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_comp, hτ, hβ,
    dgGluingSimplexConstantEdgePullback]
  exact dgGluingIdentityCommaAugmentationUnitEdge_eq R E A


end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
