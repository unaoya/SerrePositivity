module

public import SerrePositivity.InfinityCategories.HomotopyLimits.PresheafApexRepresentative
public import SerrePositivity.InfinityCategories.HomotopyLimits.SigmaPresheafColimitLegClasses

/-!
概要：実際の有限錐像と標準有限積全錐の間で、同じ coslice 代表の頂点辺を保持する。
方針：実際の評価頂点・標準余極限頂点の等式だけで両端を揃える。
規約：全脚で同じ頂点代表を共有し、元の可逆辺の全一単体を変更しない。
使われ方：完成済み全脚正方形の全錐移送判定への入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {B C : SSet.{u}}
  (r : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SigmaPresheafInfinity C)
  (q : JoinCocone (r ≫ sigmaPresheafInfinityInclusion C))
  (hq : ∀ x : ((SSet.uliftFunctor.{u + 1, u}).obj C.op) _⦋0⦌,
    IsColimitCone (F1B.kanPostcomposeCocone (evaluateFunctorAt x) q))
  {J : Type u} [Finite J] [Nonempty J] {p : nerve (Discrete J) ⟶ C.op} (c : JoinCone p)
local notation "x₀" => JoinCone.vertex (JoinCone.ulift c)
local notation "A" => sigmaPresheafVertexEvaluation r x₀
local notation "G" => sigmaPresheafFiniteEvaluationFamily r (p := p)

/-- 同じ元の頂点比較辺を、実際の全錐像と標準全錐の同じ頂点間で保持する。 -/
def sigmaColimitApexComparisonEdge :
    SSet.Edge (mapJoinCone (presheafCoconeVertexFunctor q) (JoinCone.ulift c)).vertex
      (sigmaPresheafColimitFiniteCone r c).vertex :=
  (SSet.Edge.ofTruncated (presheafEvaluationComparisonApexEdge
    (r ≫ sigmaPresheafInfinityInclusion C) q hq x₀)).ofEq
      ((presheafCoconeEvaluation_vertex q x₀).trans
        (mapJoinCone_vertex (presheafCoconeVertexFunctor q) (JoinCone.ulift c)).symm)
      ((F2.coherentDiagramTotalCocone_vertex A).trans
        ((spaceInfinityVertex_eq_coherent (F2.coherentDiagramTotalKanObject A)).trans
          (sigmaPresheafColimitFiniteCone_vertex r c).symm))

/-- 同じ元の各点比較辺を、実際の図式と標準全錐の図式の同じ成分間で保持する。 -/
def sigmaColimitComponentComparisonEdge (j : J) :
    SSet.Edge
      (((SSet.uliftFunctor.{u + 1, u}).map p ≫ presheafCoconeVertexFunctor q).app
        (Opposite.op ⦋0⦌) (ULift.up (nerveVertex (Discrete.mk j))))
      ((kanDiagramCoherentNerve (Discrete.functor
        (fun j => F2.coherentDiagramTotalKanObject (G j)))).app (Opposite.op ⦋0⦌)
          (ULift.up (nerveVertex (Discrete.mk j)))) :=
  (SSet.Edge.ofTruncated (presheafEvaluationComparisonApexEdge
    (r ≫ sigmaPresheafInfinityInclusion C) q hq
    (ULift.up (p.app (Opposite.op ⦋0⦌) (nerveVertex (Discrete.mk j)))))).ofEq
      (presheafCoconeEvaluation_vertex q _)
      ((F2.coherentDiagramTotalCocone_vertex (G j)).trans
        (kanDiagramCoherentNerve_vertex (Discrete.functor
          (fun j => F2.coherentDiagramTotalKanObject (G j))) (Discrete.mk j)).symm)

/-- 元の全錐頂点間へ正規化しても、同じ元の頂点比較辺は可逆。 -/
lemma sigmaColimitApexComparisonEdge_isInvertible :
    IsInvertibleEdge (X := SpaceInfinity.{u})
      (sigmaColimitApexComparisonEdge r q hq c).toTruncated := by
  apply (isInvertibleEdge_congr
    (e := (sigmaColimitApexComparisonEdge r q hq c).toTruncated)
    (f := presheafEvaluationComparisonApexEdge
      (r ≫ sigmaPresheafInfinityInclusion C) q hq x₀) rfl).mpr
  exact presheafEvaluationComparisonApexEdge_isInvertible _ _ _ _

omit [Finite J] [Nonempty J] in
/-- 元の図式成分間へ正規化しても、同じ元の各点比較辺は可逆。 -/
lemma sigmaColimitComponentComparisonEdge_isInvertible (j : J) :
    IsInvertibleEdge (X := SpaceInfinity.{u})
      (sigmaColimitComponentComparisonEdge r q hq (p := p) j).toTruncated := by
  apply (isInvertibleEdge_congr
    (e := (sigmaColimitComponentComparisonEdge r q hq (p := p) j).toTruncated)
    (f := presheafEvaluationComparisonApexEdge (r ≫ sigmaPresheafInfinityInclusion C) q hq
      (ULift.up (p.app (Opposite.op ⦋0⦌) (nerveVertex (Discrete.mk j))))) rfl).mpr
  exact presheafEvaluationComparisonApexEdge_isInvertible _ _ _ _

end SerrePositivity.InfinityCategories.HomotopyLimits
