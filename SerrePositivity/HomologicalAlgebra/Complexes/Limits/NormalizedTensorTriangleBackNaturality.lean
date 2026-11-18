module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorElementEvaluationJoin
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorTrianglePieces
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedSlice

/-!
概要：元の三相部分単体は、退化を含む全作用素と厳密に可換である。
方針：元の cone・全 pinched 写像・通常評価余錐 join の自然性を使う。
規約：同じ実単体・時刻を保つ。使われ方：全三相データと大域三角形の接合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorElementEvaluatedColumn_closed_pullback_map {n m : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluatedColumn A X Y c ⋙
      _root_.SerrePositivity.ComplexLimits.complexToClosed A)).pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom θ.toOrderHom) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluatedColumn A X Y
      ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) ⋙ _root_.SerrePositivity.ComplexLimits.complexToClosed A) := by
  let d := (SimplexCategory.toCat.map θ).toFunctor ⋙ c
  let F := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluatedColumn A X Y c ⋙ _root_.SerrePositivity.ComplexLimits.complexToClosed A)
  let G := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluatedColumn A X Y d ⋙ _root_.SerrePositivity.ComplexLimits.complexToClosed A)
  have hn : SSet.stdSimplex.map θ ≫ (SSet.yonedaEquiv (X := nerve
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y))).symm c = SSet.yonedaEquiv.symm d := by
    rw [SSet.yonedaEquiv_symm_naturality_left]
    rfl
  apply (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A))).symm.injective
  change SSet.yonedaEquiv.symm ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A)).map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend θ).op F) = SSet.yonedaEquiv.symm G
  rw [← SSet.yonedaEquiv_symm_naturality_left]
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso m 0).hom).mp
  calc
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso m 0).hom ≫ (SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend θ) ≫
        SSet.yonedaEquiv.symm F) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.stdSimplex.map θ) (𝟙 (Δ[0] : SSet.{u + 1})) ≫
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫ SSet.yonedaEquiv.symm F) := by
      rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinStdSimplexIso_rightPoint_naturality, Category.assoc]
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.stdSimplex.map θ) (𝟙 (Δ[0] : SSet.{u + 1})) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.yonedaEquiv.symm c) (𝟙 Δ[0]) ≫
          _root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluationJoin A X Y) := by
      rw [_root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluationJoin_restrict_simplex A X Y c]
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.yonedaEquiv.symm d) (𝟙 (Δ[0] : SSet.{u + 1})) ≫
        _root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluationJoin A X Y := by
      rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, hn, Category.id_comp]
    _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso m 0).hom ≫ SSet.yonedaEquiv.symm G :=
      _root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluationJoin_restrict_simplex A X Y d

lemma normalizedTensorTriangleBack_pullback_map {n m : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleBack A X Y c τ).pullback θ.toOrderHom =
      _root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleBack A X Y
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) (τ.comp θ.toOrderHom) := by
  unfold _root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleBack
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_comp, _root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex_reindex, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_comp,
    _root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluatedColumn_closed_pullback_map]

end SerrePositivity.ComplexLimits
