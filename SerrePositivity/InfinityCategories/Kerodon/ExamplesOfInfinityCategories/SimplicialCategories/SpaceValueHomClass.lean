module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.SpaceHomotopyClasses
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.SpaceEdgeValue
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalFunctorHom

/-!
概要：元の空間頂点の Kan 値の全写像を、端点を正規化した空間のホモトピー圏で読む。
方針：元の coherent 辺の類を、指定頂点の表示へ等号で移送する。
規約：各点の像でなく、Kan 値の写像全体を比較する。
使われ方：G8 の指定頂点同型と値の比較から全族同型への復帰。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Project.FilteredExchange

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

/-- 概要：元の指定空間の Kan 値の実写像を、同じ端点のホモトピー圏の射で読む。
方針：coherent 辺の類を元の頂点の表示へ移送する。
規約：元の射を保持。使われ方：値比較の全族自然性の照合。 -/
def spaceValueHomClass {x y : SpaceInfinity.{u} _⦋0⦌}
    (f : spaceInfinityObject x ⟶ spaceInfinityObject y) :
    (HomotopyCategory.mk x : hoFunctor.obj SpaceInfinity.{u}) ⟶ HomotopyCategory.mk y :=
  eqToHom (congrArg HomotopyCategory.mk (coherentNerveVertex_object x)).symm ≫
    SSet.Truncated.HomotopyCategory.homMk (coherentNerveEdge f).toTruncated ≫
      eqToHom (congrArg HomotopyCategory.mk (coherentNerveVertex_object y))

/-- 概要：同じ空間辺の Kan 値を読んだ類は、元の辺の類そのもの。
方針：既存の coherent 辺の回収公式と端点の移送を使う。
規約：辺の実代表を保持。使われ方：選んだ値比較の順射の類。 -/
lemma spaceValueHomClass_edgeValue {x y : SpaceInfinity.{u} _⦋0⦌}
    (e : SpaceInfinity.{u}.Edge x y) :
    spaceValueHomClass (spaceInfinityEdgeValue e) =
      SSet.Truncated.HomotopyCategory.homMk e.toTruncated :=
  homMk_transport (coherentNerveVertex_object x) (coherentNerveVertex_object y)
    (coherentNerveEdge (spaceInfinityEdgeValue e)).toTruncated e.toTruncated
      (spaceInfinityEdgeValue_edge e)

/-- 概要：元の Kan 値の写像の合成を読む操作は合成を保つ。
方針：既存の同じ coherent 合成三角形と中間端点の移送の相殺を使う。
規約：写像全体の類。使われ方：値の自然性の正方形。 -/
lemma spaceValueHomClass_comp {x y z : SpaceInfinity.{u} _⦋0⦌}
    (f : spaceInfinityObject x ⟶ spaceInfinityObject y)
    (g : spaceInfinityObject y ⟶ spaceInfinityObject z) :
    spaceValueHomClass (f ≫ g) = spaceValueHomClass f ≫ spaceValueHomClass g := by
  unfold spaceValueHomClass
  rw [← SSet.Truncated.HomotopyCategory.homMk_comp_homMk (coherentNerveCompStruct f g)]
  simp [Category.assoc]

/-- 概要：同じ端点の値の全写像の類の等式から、元の全写像間の同型を得る。
方針：端点移送を相殺し、既存の Kan 値のホモトピーの回収を使う。
規約：点ごとの一致ではない。使われ方：G8 の値比較の全族同型への復帰。 -/
def spaceValueFunctorIso_of_homClass_eq {x y : SpaceInfinity.{u} _⦋0⦌}
    (f g : spaceInfinityObject x ⟶ spaceInfinityObject y)
    (h : spaceValueHomClass f = spaceValueHomClass g) : FunctorIso f g := by
  unfold spaceValueHomClass at h
  have hh := (cancel_epi
    (eqToHom (congrArg HomotopyCategory.mk (coherentNerveVertex_object x)).symm)).mp h
  have h' := (cancel_mono
    (eqToHom (congrArg HomotopyCategory.mk (coherentNerveVertex_object y)))).mp hh
  exact functorIsoOfSimplicialHomotopy (spaceInfinity_homotopy_of_homMk_eq h').some

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
