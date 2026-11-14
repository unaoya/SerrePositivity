module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SigmaPresheafEvaluationCones
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.FiniteShapes.FiniteFamilyProductComparison

/-!
概要：P_Σ の元の評価全錐を、元の有限関手族の積全錐へ比較する。
方針：元の底図式を全頂点で厳密に照合し、既に証明した極限性を同じ錐に移す。
規約：比較元の極限性は元の前層の条件から供給し、新たな仮定にしない。
使われ方：sifted 余極限の有限積保存で、元の頂点・全脚・全錐を保持する。

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
variable {B C : SSet.{u}}
  (r : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity C)
  {J : Type u} {p : nerve (Discrete J) ⟶ C.op}

/-- 元の有限離散図式の各対象における、元の P_Σ の族の評価。 -/
def sigmaPresheafFiniteEvaluationFamily (j : J) :
    (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafVertexEvaluation r
    (ULift.up (p.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk j))))

/-- 元の交換評価図式は、元の各対象で評価した関手族の図式そのもの。 -/
lemma sigmaPresheafEvaluationDiagram_eq :
    (SSet.uliftFunctor.{u + 1, u}).map p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafFamilyFlip r =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyFunctorDiagram (sigmaPresheafFiniteEvaluationFamily r (p := p)) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.liftedDiscreteDiagram_ext
  intro j
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafFamilyFlip r).app _
    (ULift.up (p.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex j))) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafFamilyFlip, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.internalHomFlipHomEquiv_app_zero,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyFunctorDiagram_vertex]
  rfl

/-- 元の評価全錐を、同じ元の関手族の図式上に厳密に戻す。 -/
def sigmaPresheafFamilyComparisonCone (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyFunctorDiagram (sigmaPresheafFiniteEvaluationFamily r (p := p))) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafEvaluationCone r c).cast (sigmaPresheafEvaluationDiagram_eq r)

/-- 比較元の元の全錐は、各前層の有限積保存から実際に極限錐となる。 -/
lemma sigmaPresheafFamilyComparisonCone_isLimit [Finite J]
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (sigmaPresheafFamilyComparisonCone r c) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafEvaluationCone_isLimit r c hc).cast (sigmaPresheafEvaluationDiagram_eq r)

/-- 同じ図式への照合は、元の頂点での評価関手を保持する。 -/
lemma sigmaPresheafFamilyComparisonCone_vertex (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) :
    (sigmaPresheafFamilyComparisonCone r c).vertex =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafVertexEvaluation r (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1} c).vertex) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafEvaluationCone_vertex r c

/-- 元の P_Σ の条件が供給した全錐と、元の積全錐の同じ slice 内の比較。 -/
def sigmaPresheafFiniteProductConeComparison [Finite J] [Nonempty J]
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyFunctorProductConeComparison (sigmaPresheafFiniteEvaluationFamily r (p := p))
    (sigmaPresheafFamilyComparisonCone r c) (sigmaPresheafFamilyComparisonCone_isLimit r c hc)

/-- 元の評価全錐と元の反復積全錐の、全関手を保持する同型。 -/
def sigmaPresheafFiniteProductWholeConeIso [Finite J] [Nonempty J]
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyFunctorProductWholeConeIso (sigmaPresheafFiniteEvaluationFamily r (p := p))
    (sigmaPresheafFamilyComparisonCone r c) (sigmaPresheafFamilyComparisonCone_isLimit r c hc)

/-- 元の錐頂点での評価関手と元の反復積関手の coherent な同型。 -/
def sigmaPresheafFiniteProductApexIso [Finite J] [Nonempty J]
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafVertexEvaluation r (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1} c).vertex)
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyCoherentProduct (sigmaPresheafFiniteEvaluationFamily r (p := p))) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyFunctorProductApexIso (sigmaPresheafFiniteEvaluationFamily r (p := p))
    (sigmaPresheafFamilyComparisonCone r c) (sigmaPresheafFamilyComparisonCone_isLimit r c hc)
    _ (sigmaPresheafFamilyComparisonCone_vertex r c)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
