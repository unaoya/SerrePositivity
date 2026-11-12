module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FixedApexConeFiber
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopConeFixedApexComparison
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaFiberIntervalIso

/-!
概要：固定頂点の錐と、元の図式固定の二段 fiber を同じ全空間の上で厳密に同定する。
方針：同じ円柱の厳密な式を照合し、証明済みの実区間族の同値性を戻す。
規約：安定性や有限余極限を先取りしない。使われ方：一般安定性判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 固定頂点からの同じ実 cospan の全錐を、元の図式固定 fiber と厳密に同型にする。 -/
def loopConeFixedApexDiagramFiberIso {X : SSet.{u}} [Quasicategory X]
    {y : X _⦋0⦌} (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopSquare y) (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedApexConeFamily (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan t.square) x ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeSourceFiberProjection X x) t.diagramVertex :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.fixedApexPointedConeDiagramFiberIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan t.square) x ≪≫
    (eqToIso (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pointedConeProjection (horn 2 2 : SSet.{u}) X x))
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramConeFamily_base_vertex t))).symm ≪≫
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeSourceDiagramFiberIso X x t.diagramVertex).symm

/-- 図式固定 fiber 表示の逆射は、元の全錐への二重包含を回収する。 -/
lemma loopConeSourceDiagramFiberIso_inv_diagram {X : SSet.{u}} [Quasicategory X]
    (x : X _⦋0⦌) (d : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeSourceDiagramFiberIso X x d).inv ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeSourceFiberProjection X x) d ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeObjectSource X) x ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeObjectDiagram X =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pointedConeProjection (horn 2 2 : SSet.{u}) X x)
        ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramConeFamily X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.limitConeProjection (horn 2 2 : SSet.{u}) X).app
          (Opposite.op ⦋0⦌) d) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.coneApexEvaluation (horn 2 2 : SSet.{u}) X) x := by
  let e := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeSourceDiagramFiberIso X x d
  have hdiag : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeSourceFiberDiagram X x ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.coneApexEvaluation (horn 2 2 : SSet.{u}) X) x =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeObjectSource X) x ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeObjectDiagram X :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι _ _ _ _ _
  have hh := congrArg (fun f ↦ e.inv ≫ f ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.coneApexEvaluation (horn 2 2 : SSet.{u}) X) x)
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeSourceDiagramFiberIso_hom_ι X x d)
  simpa only [e, Category.assoc, hdiag, Iso.inv_hom_id_assoc] using hh.symm

/-- 固定頂点の錐の厳密同型は、同じ元の全錐の評価を保持する。 -/
lemma loopConeFixedApexDiagramFiberIso_diagram {X : SSet.{u}} [Quasicategory X]
    {y : X _⦋0⦌} (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopSquare y) (x : X _⦋0⦌) :
    (loopConeFixedApexDiagramFiberIso t x).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeSourceFiberProjection X x) t.diagramVertex ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeObjectSource X) x ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeObjectDiagram X =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedApexConeFamilyEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan t.square) x := by
  dsimp only [loopConeFixedApexDiagramFiberIso, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc]
  rw [loopConeSourceDiagramFiberIso_inv_diagram]
  have hi := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexFiberι_eqTransport
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pointedConeProjection (horn 2 2 : SSet.{u}) X x)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramConeFamily_base_vertex t).symm
  have hi' : (eqToIso (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pointedConeProjection (horn 2 2 : SSet.{u}) X x))
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramConeFamily_base_vertex t))).inv ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pointedConeProjection (horn 2 2 : SSet.{u}) X x)
        ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramConeFamily X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.limitConeProjection (horn 2 2 : SSet.{u}) X).app
          (Opposite.op ⦋0⦌) t.diagramVertex) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pointedConeProjection (horn 2 2 : SSet.{u}) X x)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan t.square)) := hi
  rw [reassoc_of% hi']
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.fixedApexPointedConeDiagramFiberIso_hom_ι _ _

/-- 厳密同型を元の全空間へ含めると、同じ実 lift そのものになる。 -/
lemma loopConeFixedApexDiagramFiberIso_lift {X : SSet.{u}} [Quasicategory X]
    {y : X _⦋0⦌} (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopSquare y) (x : X _⦋0⦌) :
    (loopConeFixedApexDiagramFiberIso t x).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeSourceFiberProjection X x) t.diagramVertex ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeObjectSource X) x = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeFixedApexLift t x := by
  apply pullback.hom_ext
  · exact (loopConeFixedApexDiagramFiberIso_diagram t x).trans
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeFixedApexLift_diagram t x).symm
  · change (loopConeFixedApexDiagramFiberIso t x).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeSourceFiberProjection X x) t.diagramVertex ≫
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeSourceFiberProjection X x = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeFixedApexLift_loop]
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
