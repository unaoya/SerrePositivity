module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopConeSourceFiber
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaFiberLeftFibration
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.VertexFiberSquareIso
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftUnstraighteningFiberIso
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LeftFibrationFiberComparison
/-!
概要：実 loop 錐の comma 比較を図式固定 fiber へ制限する。
方針：二段の厳密 fiber と pullback の同型を照合し、同じ実射に F1 の判定を適用する。
規約：fiber 同値性の仮定を明示し、まだ全錐比較の同値性とは主張しない。
使われ方：一般安定性判定の実境界比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 同じ実 comma 比較を、loop 図式固定の厳密 fiber へ制限する。 -/
def loopConeClassifierDiagramFiberMap (X : SSet.{u}) [Quasicategory X] (x : X _⦋0⦌)
    (d : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeSourceFiberProjection X x) d ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberProjection (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0) x) d :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeSourceFiberProjection X x)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberProjection (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0) x)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeClassifierSourceFiberMap X x) (by
      simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberProjection, Category.assoc,
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeSourceFiberProjection] using _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeClassifierSourceFiberMap_target X x) d

/-- 図式固定 fiber を、固定錐頂点からの対応する錐 fiber と同型にする。 -/
def loopConeSourceDiagramFiberIso (X : SSet.{u}) [Quasicategory X] (x : X _⦋0⦌)
    (d : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeSourceFiberProjection X x) d ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pointedConeProjection (horn 2 2 : SSet.{u}) X x)
        ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramConeFamily X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.limitConeProjection (horn 2 2 : SSet.{u}) X).app
          (Opposite.op ⦋0⦌) d) := by
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pointedConeProjection (horn 2 2 : SSet.{u}) X x
  let P := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramConeFamily X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.limitConeProjection (horn 2 2 : SSet.{u}) X
  let e := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeSourceFiber_isPullback X x).isoPullback
  have he : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeSourceFiberProjection X x ≫ (Iso.refl (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X)).hom =
      e.hom ≫ pullback.snd q P := by
    simpa only [Iso.refl_hom, Category.comp_id] using
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeSourceFiber_isPullback X x).isoPullback_hom_snd.symm
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexFiberSquareIso (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeSourceFiberProjection X x) (pullback.snd q P)
    e (Iso.refl _) he d ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberPullbackIso q P d
/-- 図式固定 fiber 同型は元の実錐への包含と可換。 -/
lemma loopConeSourceDiagramFiberIso_hom_ι (X : SSet.{u}) [Quasicategory X] (x : X _⦋0⦌)
    (d : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X) _⦋0⦌) :
    (loopConeSourceDiagramFiberIso X x d).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pointedConeProjection (horn 2 2 : SSet.{u}) X x)
        ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramConeFamily X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.limitConeProjection (horn 2 2 : SSet.{u}) X).app
          (Opposite.op ⦋0⦌) d) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeSourceFiberProjection X x) d ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeSourceFiberDiagram X x := by
  dsimp only [loopConeSourceDiagramFiberIso, Iso.trans_hom]
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberPullbackIso_hom_ι, ← Category.assoc]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexFiberSquareIso, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexFiberSquareHom,
    Iso.refl_hom, NatTrans.id_app, CategoryTheory.types_id_apply, Category.assoc]
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι, Category.assoc, IsPullback.isoPullback_hom_fst]

/-- 図式固定 fiber の比較は元の実 comma 比較への包含と可換。 -/
lemma loopConeClassifierDiagramFiberMap_ι (X : SSet.{u}) [Quasicategory X] (x : X _⦋0⦌)
    (d : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X) _⦋0⦌) :
    loopConeClassifierDiagramFiberMap X x d ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberProjection (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0) x) d =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeSourceFiberProjection X x) d ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeClassifierSourceFiberMap X x :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι _ _ _ _ _
/-- 同じ実 fiber 比較が各図式上で同値なら、始点固定比較も同値。 -/
lemma loopConeClassifierSourceFiberMap_isQCatEquivalence_of_diagramFibers
    (X : SSet.{u}) [Quasicategory X] (x : X _⦋0⦌)
    (h : ∀ d : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X) _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (loopConeClassifierDiagramFiberMap X x d)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeClassifierSourceFiberMap X x) := by
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberProjection (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0) x
  let : Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0) x) :=
    quasicategory_of_innerFibration q
  have hf : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeClassifierSourceFiberMap X x ≫ q = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeSourceFiberProjection X x := by
    simpa only [q, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberProjection, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeSourceFiberProjection] using _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeClassifierSourceFiberMap_target X x
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isQCatEquivalence_of_leftFibration_fibers (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeSourceFiberProjection X x) q
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeClassifierSourceFiberMap X x) hf h
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
