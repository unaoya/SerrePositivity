module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.OppositeFunctorIso
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexFiberOpposite
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FibersBaseIso

/-!
概要：相対関手空間の単体順序の反転は、反転した射影と図式の相対関手空間と同型。
方針：fiber の反転、底の内部 Hom 同型、全空間の内部 Hom 同型を順に合成する。
規約：底上の射の向きは変えず、パラメーターの単体順序だけを反転する。
使われ方：right fibrations の元の相対 Hom を left fibrations の相対 Hom へ比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

/-- 反転した元の相対 Hom と、反転した同じ射影・図式の相対 Hom の厳密な同型。 -/
def relativeFunctorOppositeIso {A E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p a).op ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace (SSet.opFunctor.map p) (SSet.opFunctor.map a) := by
  let b := SSet.opObjEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a)
  let eB := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso A B
  let eE := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso A E
  let r := SSet.opFunctor.map ((ihom A).map p)
  let s := (ihom A.op).map (SSet.opFunctor.map p)
  have he : eE.hom ≫ s = r ≫ eB.hom :=
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHom_post A p).symm
  exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.vertexFiberOpIso ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a) ≪≫
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.vertexFiberBaseIso r eB b ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.vertexFiberIsoOfTotalIso (r ≫ eB.hom) s eE he (eB.hom.app _ b) ≪≫
    eqToIso (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber s) (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.oppositeInternalHomIso_vertex a))

/-- fiber の頂点の等式による移送は、同じ全空間への包含を保つ。 -/
lemma vertexFiber_eqToIso_ι {E B : SSet.{u}} (p : E ⟶ B)
    {b c : B _⦋0⦌} (h : b = c) :
    (eqToIso (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p) h)).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p c = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b := by
  cases h
  exact Category.id_comp _

/-- この相対 Hom の反転同型は、内部 Hom への包含の後で標準反転比較となる。 -/
lemma relativeFunctorOppositeIso_hom_ι {A E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B) :
    (relativeFunctorOppositeIso p a).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom A.op).map (SSet.opFunctor.map p))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.opFunctor.map a)) =
    SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a)) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso A E).hom := by
  unfold relativeFunctorOppositeIso
  simp only [Iso.trans_hom, Category.assoc]
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.vertexFiberIsoOfTotalIso]
  rw [vertexFiber_eqToIso_ι _ (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.oppositeInternalHomIso_vertex a)]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι]
  rw [← Category.assoc _ _ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso A E).hom,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.vertexFiberBaseIso_hom_ι]
  rfl

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
