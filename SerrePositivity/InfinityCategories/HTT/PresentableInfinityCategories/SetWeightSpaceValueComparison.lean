module

public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetSections
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.SpaceValueHomClass

/-!
概要：G8 が選んだ頂点同型の同じ値比較を、ホモトピー圏の正方形から全族で比較する。
方針：元の選択した辺の類を回収し、Kan 値の全写像間のホモトピーへ戻す。
規約：正本の spaceValueEquivalence の順射を保持する。
使われ方：指定極限頂点と表現の頂点同型の自然性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Project.FilteredExchange
open SerrePositivity.InfinityCategories.Project.SetWeightedTensors

namespace SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories

/-- 概要：正本の選んだ値比較の順射の類は、元の頂点同型の順射そのもの。
方針：正本が選ぶ同じ辺の代表と既存の値の回収を使う。
規約：選んだ順射を変更しない。使われ方：G8 の値比較の自然性の照合。 -/
lemma spaceValueHomClass_spaceValueEquivalence {x y : SpaceInfinity.{u} _⦋0⦌}
    (e : VertexIso x y) :
    spaceValueHomClass (SetWeight.spaceValueEquivalence e).hom = e.hom := by
  let a := (homotopyCategory_homMk_surjective x y e.hom).choose
  change spaceValueHomClass (spaceInfinityEdgeValue (SSet.Edge.ofTruncated a)) = e.hom
  rw [spaceValueHomClass_edgeValue]
  exact (homotopyCategory_homMk_surjective x y e.hom).choose_spec

/-- 概要：空間のホモトピー圏で可換な正方形は、正本の同じ値比較による全写像間の同型を与える。
方針：元の値の全写像の類を正方形へ戻し、既存のホモトピー回収を使う。
規約：各点の像でなく写像全体の同型。使われ方：G8 の選択した頂点同型の接続。 -/
def setWeightSpaceValueSquareIso {x₀ x₁ y₀ y₁ : SpaceInfinity.{u} _⦋0⦌}
    (s : VertexIso x₀ x₁) (t : VertexIso y₀ y₁)
    (a : SpaceInfinity.{u}.Edge x₀ y₀) (b : SpaceInfinity.{u}.Edge x₁ y₁)
    (h : SSet.Truncated.HomotopyCategory.homMk a.toTruncated ≫ t.hom =
      s.hom ≫ SSet.Truncated.HomotopyCategory.homMk b.toTruncated) :
    FunctorIso (spaceInfinityEdgeValue a ≫ (SetWeight.spaceValueEquivalence t).hom)
      ((SetWeight.spaceValueEquivalence s).hom ≫ spaceInfinityEdgeValue b) := by
  apply spaceValueFunctorIso_of_homClass_eq (x := x₀) (y := y₁)
  erw [spaceValueHomClass_comp (x := x₀) (y := y₀) (z := y₁)
      (spaceInfinityEdgeValue a) (SetWeight.spaceValueEquivalence t).hom,
    spaceValueHomClass_comp (x := x₀) (y := x₁) (z := y₁)
      (SetWeight.spaceValueEquivalence s).hom (spaceInfinityEdgeValue b),
    spaceValueHomClass_edgeValue, spaceValueHomClass_spaceValueEquivalence,
    spaceValueHomClass_spaceValueEquivalence, spaceValueHomClass_edgeValue]
  exact h

end SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories
