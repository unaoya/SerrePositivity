module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SliceDiagramIso
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeEquiv
public import SerrePositivity.InfinityCategories.HTT.Section6_1_2.OppositeIso

/-!
概要：通常の余錐と nerve の余錐を反転によって比較する。
方針：反対圏の nerve の同型と slice の同型を合成する。
規約：図式・余錐・頂点を固定し、同じ宇宙の小さい圏を扱う。
使われ方：B5 の局所余極限と pointwise Kan の古典比較。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

variable {I C : Type u} [Category.{u} I] [Category.{u} C] {F : I ⥤ C}

/-- 概要：反対圏の nerve の slice と反転図式の slice を同型にする。
方針：反転と図式同型の射影公式を使う。
規約：指定した元の図式と余錐を保持する。
使われ方：B5 の局所余極限の双方向比較。 -/
def nerveOppositeSliceIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (nerveMap F.op) ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.opFunctor.map (nerveMap F)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceDiagramIso (_root_.SerrePositivity.InfinityCategories.HTT.Section6_1_2.nerveOppositeIso I) (_root_.SerrePositivity.InfinityCategories.HTT.Section6_1_2.nerveOppositeIso C) _ _
    (_root_.SerrePositivity.InfinityCategories.HTT.Section6_1_2.nerveOppositeIso_natural I F)

/-- 概要：余錐の反転を全単射として束ねる。
方針：反転と図式同型の射影公式を使う。
規約：指定した元の図式と余錐を保持する。
使われ方：B5 の局所余極限の双方向比較。 -/
def coconeReverseConeEquiv {K X : SSet.{u}} (p : K ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p ≃ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (SSet.opFunctor.map p) :=
  (SSet.opObjEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) (n := Opposite.op ⦋0⦌)).symm.trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isoVertexEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceUnderOpIso p))

/-- 概要：通常の余錐と反対図式の錐の全単射。
方針：反転と図式同型の射影公式を使う。
規約：指定した元の図式と余錐を保持する。
使われ方：B5 の局所余極限の双方向比較。 -/
def coconeOpEquiv : Cocone F ≃ Cone F.op where
  toFun := Cocone.op
  invFun := Cone.unop
  left_inv _ := rfl
  right_inv _ := rfl

/-- 概要：通常の余錐と nerve の任意の native な余錐の全単射。
方針：反転と図式同型の射影公式を使う。
規約：指定した元の図式と余錐を保持する。
使われ方：B5 の局所余極限の双方向比較。 -/
def nerveCoconeEquiv : Cocone F ≃ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (nerveMap F) :=
  (coconeOpEquiv (F := F)).trans ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveConeEquiv (F := F.op)).trans
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isoVertexEquiv (nerveOppositeSliceIso (F := F))).trans
      (coconeReverseConeEquiv (nerveMap F)).symm))

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
