module

public import SerrePositivity.KST.Spectra.PointedKanReplacement
public import SerrePositivity.KST.Spectra.PointedGroupProduct
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyIso

/-!
概要：元の点つき Kan 置換による零射の正次数群上の作用。
方針：同じ一つの点の置換を経由させ、anodyne 単位で群の消滅を移す。
規約：置換が零射を厳密に保存するとは仮定しない。
使われ方：一重 S• 加法性の標準軸の計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomotopicalAlgebra CartesianMonoidalCategory SSet
open SSet.modelCategoryQuillen
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective
local instance (X : PointedSimplicialSet.{u}) :
    KanComplex (PointedKanReplacement.functor.obj X).right :=
  PointedKanReplacement.obj_kanComplex X

/-- 同じ一つの点の Kan 置換の正次数群は自明。 -/
lemma kanReplacementPoint_group_subsingleton (n : ℕ) :
    Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup
      (PointedKanReplacement.obj (PointedObject.point : PointedSimplicialSet.{u})).right n
      (PointedKanReplacement.obj (PointedObject.point : PointedSimplicialSet.{u})).basepoint) := by
  let P : PointedSimplicialSet.{u} := PointedObject.point
  have : IsIso (terminal.from P.right) :=
    isIso_of_isTerminal isTerminalTensorUnit terminalIsTerminal _
  have : KanComplex P.right := by
    change Fibration (terminal.from P.right)
    infer_instance
  have : Subsingleton (P.right.PtSimplex (n + 1) P.basepoint) := ⟨by
    intro a b
    apply RelativeMorphism.ext
    exact isTerminalTensorUnit.hom_ext _ _⟩
  have : Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup P.right n P.basepoint) := by
    unfold _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup
    infer_instance
  let i : P ⟶ PointedKanReplacement.obj P := PointedKanReplacement.unit.app P
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfPiIsomorphism n i.right
    (PointedKanReplacement.unit_piIsomorphism P)
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint i)).symm.injective.subsingleton

/-- 零射の実 Kan 置換は、全ての正次数の群で零準同型として作用する。 -/
theorem pointedKanReplacement_zero_group (X Y : PointedSimplicialSet.{u}) (n : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (PointedKanReplacement.obj X).right n
      (PointedKanReplacement.obj X).basepoint) :
    pointedGroupMap n (PointedKanReplacement.map (0 : X ⟶ Y)) a = 1 := by
  have := kanReplacementPoint_group_subsingleton.{u} n
  have h : (0 : X ⟶ Y) = PointedObject.toPoint X ≫ PointedObject.fromPoint Y :=
    (PointedObject.toPoint_comp_fromPoint X Y).symm
  rw [h]
  change pointedGroupMap n (PointedKanReplacement.functor.map (_ ≫ _)) a = _
  rw [CategoryTheory.Functor.map_comp, pointedGroupMap_comp]
  change pointedGroupMap n (PointedKanReplacement.map (PointedObject.fromPoint Y))
    (pointedGroupMap n (PointedKanReplacement.map (PointedObject.toPoint X)) a) = 1
  have hz : pointedGroupMap n (PointedKanReplacement.map (PointedObject.toPoint X)) a = 1 :=
    Subsingleton.elim _ _
  rw [hz, map_one]

end SerrePositivity.KST.NonConnective
