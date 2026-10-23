module

public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaPresheafEvaluationCones
public import SerrePositivity.InfinityCategories.HomotopyLimits.FiniteFamilyProductComparison

/-!
概要：P_Σ の元の評価全錐を、元の有限関手族の積全錐へ比較する。
方針：元の底図式を全頂点で厳密に照合し、既に証明した極限性を同じ錐に移す。
規約：比較元の極限性は元の前層の条件から供給し、新たな仮定にしない。
使われ方：sifted 余極限の有限積保存で、元の頂点・全脚・全錐を保持する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {B C : SSet.{u}}
  (r : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SigmaPresheafInfinity C)
  {J : Type u} {p : nerve (Discrete J) ⟶ C.op}

/-- 元の有限離散図式の各対象における、元の P_Σ の族の評価。 -/
def sigmaPresheafFiniteEvaluationFamily (j : J) :
    (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u} :=
  sigmaPresheafVertexEvaluation r
    (ULift.up (p.app (Opposite.op ⦋0⦌) (nerveVertex (Discrete.mk j))))

/-- 元の交換評価図式は、元の各対象で評価した関手族の図式そのもの。 -/
lemma sigmaPresheafEvaluationDiagram_eq :
    (SSet.uliftFunctor.{u + 1, u}).map p ≫ sigmaPresheafFamilyFlip r =
      finiteFamilyFunctorDiagram (sigmaPresheafFiniteEvaluationFamily r (p := p)) := by
  apply liftedDiscreteDiagram_ext
  intro j
  change (sigmaPresheafFamilyFlip r).app _
    (ULift.up (p.app _ (nerveVertex j))) = _
  rw [sigmaPresheafFamilyFlip, internalHomFlipHomEquiv_app_zero,
    finiteFamilyFunctorDiagram_vertex]
  rfl

/-- 元の評価全錐を、同じ元の関手族の図式上に厳密に戻す。 -/
def sigmaPresheafFamilyComparisonCone (c : JoinCone p) :
    JoinCone (finiteFamilyFunctorDiagram (sigmaPresheafFiniteEvaluationFamily r (p := p))) :=
  (sigmaPresheafEvaluationCone r c).cast (sigmaPresheafEvaluationDiagram_eq r)

/-- 比較元の元の全錐は、各前層の有限積保存から実際に極限錐となる。 -/
lemma sigmaPresheafFamilyComparisonCone_isLimit [Finite J]
    (c : JoinCone p) (hc : IsLimitCone c) :
    IsLimitCone (sigmaPresheafFamilyComparisonCone r c) :=
  (sigmaPresheafEvaluationCone_isLimit r c hc).cast (sigmaPresheafEvaluationDiagram_eq r)

/-- 同じ図式への照合は、元の頂点での評価関手を保持する。 -/
lemma sigmaPresheafFamilyComparisonCone_vertex (c : JoinCone p) :
    (sigmaPresheafFamilyComparisonCone r c).vertex =
      functorVertex (sigmaPresheafVertexEvaluation r (JoinCone.ulift.{u, u + 1} c).vertex) :=
  sigmaPresheafEvaluationCone_vertex r c

/-- 元の P_Σ の条件が供給した全錐と、元の積全錐の同じ slice 内の比較。 -/
def sigmaPresheafFiniteProductConeComparison [Finite J] [Nonempty J]
    (c : JoinCone p) (hc : IsLimitCone c) :=
  finiteFamilyFunctorProductConeComparison (sigmaPresheafFiniteEvaluationFamily r (p := p))
    (sigmaPresheafFamilyComparisonCone r c) (sigmaPresheafFamilyComparisonCone_isLimit r c hc)

/-- 元の評価全錐と元の反復積全錐の、全関手を保持する同型。 -/
def sigmaPresheafFiniteProductWholeConeIso [Finite J] [Nonempty J]
    (c : JoinCone p) (hc : IsLimitCone c) :=
  finiteFamilyFunctorProductWholeConeIso (sigmaPresheafFiniteEvaluationFamily r (p := p))
    (sigmaPresheafFamilyComparisonCone r c) (sigmaPresheafFamilyComparisonCone_isLimit r c hc)

/-- 元の錐頂点での評価関手と元の反復積関手の coherent な同型。 -/
def sigmaPresheafFiniteProductApexIso [Finite J] [Nonempty J]
    (c : JoinCone p) (hc : IsLimitCone c) :
    FunctorIso (sigmaPresheafVertexEvaluation r (JoinCone.ulift.{u, u + 1} c).vertex)
      (finiteFamilyCoherentProduct (sigmaPresheafFiniteEvaluationFamily r (p := p))) :=
  finiteFamilyFunctorProductApexIso (sigmaPresheafFiniteEvaluationFamily r (p := p))
    (sigmaPresheafFamilyComparisonCone r c) (sigmaPresheafFamilyComparisonCone_isLimit r c hc)
    _ (sigmaPresheafFamilyComparisonCone_vertex r c)

end SerrePositivity.InfinityCategories.HomotopyLimits
