module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorTriangleMap
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.PrismEvaluation
/-! 概要：大域三角形の各面を元の円柱と区間族へ同定する。
方針：既存の左右 prism 評価式で全単体を同じ切断へ戻す。
規約：全 K を保持。使われ方：元の評価三角形の全関手圏での合成。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)
lemma coneTriangleBackIndex_eq_prismCut {n : ℕ} (τ : Fin (n + 1) →o Fin 3)
    (t : (Δ[1] : SSet.{u + 1}) _⦋n⦌) (ht : ∀ i, τ i = 2 ↔ t i ≠ 0) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut (SSet.stdSimplex.objEquiv t).toOrderHom = _root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex τ := by
  apply DFunLike.ext
  intro i
  change (if t i = 0 then i.castSucc else Fin.last (n + 1)) =
    (if τ i = 2 then Fin.last (n + 1) else i.castSucc)
  by_cases hi : τ i = 2
  · simp [hi, (ht i).mp hi]
  · have hti : t i = 0 := by by_contra h; exact hi ((ht i).mpr h)
    simp [hi, hti]

lemma normalizedTensorEvaluationPrism_app_triangle {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (t : (Δ[1] : SSet.{u + 1}) _⦋n⦌) (τ : Fin (n + 1) →o Fin 3)
    (ht : ∀ i, τ i = 2 ↔ t i ≠ 0) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism _ ≫ _root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluationJoin A X Y).app
      (Opposite.op ⦋n⦌) (t, c) = _root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleBack A X Y c τ := by
  have hc : SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).inv ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.yonedaEquiv.symm c) (𝟙 (Δ[0] : SSet.{u + 1})) ≫
      _root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluationJoin A X Y) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluatedColumn A X Y c ⋙ _root_.SerrePositivity.ComplexLimits.complexToClosed A) := by
    rw [_root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluationJoin_restrict_simplex, Iso.inv_hom_id_assoc,
      Equiv.apply_symm_apply]
  change (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluationJoin A X Y).app (Opposite.op ⦋n⦌)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism _).app (Opposite.op ⦋n⦌) (t, c)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.rightMappingSpacePrism_evaluate, hc, _root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex_eq_prismCut τ t ht]
  rfl

lemma normalizedTensorPinchedPrism_app_triangle {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (t : (Δ[1] : SSet.{u + 1}) _⦋n⦌) (τ : Fin (n + 1) →o Fin 3)
    (ht : ∀ i, τ i = 2 ↔ t i ≠ 0) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomUncurry
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementPinchedMap A X Y)).app (Opposite.op ⦋n⦌) (t, c) =
      _root_.SerrePositivity.ComplexLimits.normalizedTensorTrianglePinched A X Y c τ := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomUncurry (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementPinchedMap A X Y)).app (Opposite.op ⦋n⦌)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism _).app (Opposite.op ⦋n⦌) (t, c)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.rightMappingSpacePrism_evaluate, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pinchedHomUncurry_simplex,
    _root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex_eq_prismCut τ t ht]
  rfl

end SerrePositivity.ComplexLimits
