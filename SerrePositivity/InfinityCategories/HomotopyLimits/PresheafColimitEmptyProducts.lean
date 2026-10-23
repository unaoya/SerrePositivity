module

public import SerrePositivity.InfinityCategories.HomotopyLimits.PresheafCoconeVertexEvaluation
public import SerrePositivity.InfinityCategories.F2.Presentable.SiftedTerminalDiagramColimit
public import SerrePositivity.InfinityCategories.HomotopyLimits.EmptyShapeLimitCriterion
public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaPresheafEvaluationCones

/-!
概要：P_Σ の元の族の指定前層余極限頂点は、元の空添字の有限極限全錐を保存する。
方針：各元の前層の空積保存から評価図式の全値を終対象とし、指定評価余極限で回収する。
規約：元の指定余錐・頂点関手・元の全空錐を保持。底の quasicategory 性は不要。
使われ方：P_Σ の sifted 閉性の空添字の場合を実際の前層余極限頂点で供給する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

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
    (r : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SigmaPresheafInfinity C)
    {J : Type u} [Finite J] [IsEmpty J] {p : nerve (Discrete J) ⟶ C.op}
    (c : JoinCone p) (hc : IsLimitCone c)
    (b : ((SSet.uliftFunctor.{u + 1, u}).obj B) _⦋0⦌) :
    IsTerminalVertex ((sigmaPresheafVertexEvaluation r (JoinCone.ulift.{u, u + 1} c).vertex).app
      (Opposite.op ⦋0⦌) b) := by
  have h := (isLimitCone_iff_terminal_of_emptyVertices _).mp
    (sigmaPresheafEvaluationCone_isPointwiseLimit r c hc b)
  rw [evaluateFunctorCone, mapJoinCone_vertex, sigmaPresheafEvaluationCone_vertex,
    evaluateFunctorAt_functorVertex] at h
  exact h

/-- 元の指定前層余極限の同じ頂点関手は、元の空添字の有限極限全錐を保存する。 -/
lemma presheafColimitVertex_mapEmptyCone_isLimit {B C : SSet.{u}} [IsSiftedInfinity B]
    (r : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SigmaPresheafInfinity C)
    (q : JoinCocone (r ≫ sigmaPresheafInfinityInclusion C))
    (hq : ∀ x : ((SSet.uliftFunctor.{u + 1, u}).obj C.op) _⦋0⦌,
      IsColimitCone (F1B.kanPostcomposeCocone (evaluateFunctorAt x) q))
    {J : Type u} [Finite J] [IsEmpty J] {p : nerve (Discrete J) ⟶ C.op}
    (c : JoinCone p) (hc : IsLimitCone c) :
    IsLimitCone (mapJoinCone (presheafCoconeVertexFunctor q) (JoinCone.ulift.{u, u + 1} c)) := by
  apply (isLimitCone_iff_terminal_of_emptyVertices _).mpr
  rw [mapJoinCone_vertex, ← presheafCoconeEvaluation_vertex]
  exact siftedTerminalDiagramColimit_isTerminal
    (sigmaPresheafVertexEvaluation r (JoinCone.ulift.{u, u + 1} c).vertex)
    (sigmaPresheafEmptyConeEvaluation_isTerminal r c hc) _ (hq _)

/-- 実際に供給した元の前層余極限全余錐の頂点関手は、元の空添字極限全錐を保存する。 -/
lemma sigmaPresheafAmbientColimit_mapEmptyCone_isLimit {B C : SSet.{u}} [IsSiftedInfinity B]
    (r : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SigmaPresheafInfinity C)
    {J : Type u} [Finite J] [IsEmpty J] {p : nerve (Discrete J) ⟶ C.op}
    (c : JoinCone p) (hc : IsLimitCone c) :
    IsLimitCone (mapJoinCone (presheafCoconeVertexFunctor
      (presheafCoherentColimitCone (r ≫ sigmaPresheafInfinityInclusion C)))
      (JoinCone.ulift.{u, u + 1} c)) :=
  presheafColimitVertex_mapEmptyCone_isLimit r _
    (presheafCoherentColimitCone_evaluation_isColimit _) c hc

end SerrePositivity.InfinityCategories.HomotopyLimits
