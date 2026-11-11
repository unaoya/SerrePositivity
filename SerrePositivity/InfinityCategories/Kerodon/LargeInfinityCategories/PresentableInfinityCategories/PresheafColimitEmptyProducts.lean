module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.EquivalenceLimits
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorLimits
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreLimit
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.Terminal
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseLimits
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeCoconeAbsolute
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SiftedInfinity
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SiftedTerminalDiagramColimit
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SigmaPresheafEvaluationCones
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.EmptyShapeLimitCriterion
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PresheafCoconeVertexEvaluation
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PresheafCoherentColimitCones

/-!
概要：P_Σ の元の族の指定前層余極限頂点は、元の空添字の有限極限全錐を保存する。
方針：各元の前層の空積保存から評価図式の全値を終対象とし、指定評価余極限で回収する。
規約：元の指定余錐・頂点関手・元の全空錐を保持。底の quasicategory 性は不要。
使われ方：P_Σ の sifted 閉性の空添字の場合を実際の前層余極限頂点で供給する。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 空添字の離散圏の nerve は、元の頂点を持たない。 -/
instance emptyDiscreteNerveVertices (J : Type u) [IsEmpty J] :
    IsEmpty ((nerve (Discrete J)) _⦋0⦌) :=
  ⟨fun s ↦ isEmptyElim (s.obj 0).as⟩

/-- 宇宙を持ち上げた空離散形状も、元の頂点を持たない。 -/
instance emptyUliftDiscreteNerveVertices (J : Type u) [IsEmpty J] :
    IsEmpty (((SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete J))) _⦋0⦌) :=
  inferInstanceAs (IsEmpty (ULift.{u + 1} ((nerve (Discrete J)) _⦋0⦌)))

/-- 元の P_Σ の族の空錐評価図式は、各元の値が終対象。 -/
lemma sigmaPresheafEmptyConeEvaluation_isTerminal {B C : SSet.{u}}
    (r : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity C)
    {J : Type u} [Finite J] [IsEmpty J] {p : nerve (Discrete J) ⟶ C.op}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c)
    (b : ((SSet.uliftFunctor.{u + 1, u}).obj B) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafVertexEvaluation r (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1} c).vertex).app
      (Opposite.op ⦋0⦌) b) := by
  have h := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.isLimitCone_iff_terminal_of_emptyVertices _).mp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafEvaluationCone_isPointwiseLimit r c hc b)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.evaluateFunctorCone, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafEvaluationCone_vertex,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex] at h
  exact h

/-- 元の指定前層余極限の同じ頂点関手は、元の空添字の有限極限全錐を保存する。 -/
lemma presheafColimitVertex_mapEmptyCone_isLimit {B C : SSet.{u}} [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.IsSiftedInfinity B]
    (r : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity C)
    (q : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaPresheafInfinityInclusion C))
    (hq : ∀ x : ((SSet.uliftFunctor.{u + 1, u}).obj C.op) _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanPostcomposeCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt x) q))
    {J : Type u} [Finite J] [IsEmpty J] {p : nerve (Discrete J) ⟶ C.op}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafCoconeVertexFunctor q) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1} c)) := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.isLimitCone_iff_terminal_of_emptyVertices _).mpr
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone_vertex, ← _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafCoconeEvaluation_vertex]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.siftedTerminalDiagramColimit_isTerminal
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafVertexEvaluation r (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1} c).vertex)
    (sigmaPresheafEmptyConeEvaluation_isTerminal r c hc) _ (hq _)

/-- 実際に供給した元の前層余極限全余錐の頂点関手は、元の空添字極限全錐を保存する。 -/
lemma sigmaPresheafAmbientColimit_mapEmptyCone_isLimit {B C : SSet.{u}} [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.IsSiftedInfinity B]
    (r : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity C)
    {J : Type u} [Finite J] [IsEmpty J] {p : nerve (Discrete J) ⟶ C.op}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafCoconeVertexFunctor
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafCoherentColimitCone (r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaPresheafInfinityInclusion C)))
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1} c)) :=
  presheafColimitVertex_mapEmptyCone_isLimit r _
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafCoherentColimitCone_evaluation_isColimit _) c hc

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
