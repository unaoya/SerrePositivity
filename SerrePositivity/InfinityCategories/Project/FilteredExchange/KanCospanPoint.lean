module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.ContinuousKanSequence
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalDiagram
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalPullbackCoordinates
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalPullbackHomotopyPoint
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanCospanPathEndpoints

/-!
概要：元の二入力と指定 Kan path から実際の Kan 引き戻しへの射を構成する。
方針：単位の自然性で端点を移し、三座標の厳密な持ち上げを使う。
規約：入力は元の全空間への射、path は元の指定円柱。
使われ方：有限近似と輸送と値への反映を同じ標的引き戻し内で比較する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange
variable {K E D X : SSet.{u}} (f : E ⟶ X) (g : D ⟶ X) (u : K ⟶ E) (v : K ⟶ D)
  (H : SSet.Homotopy (u ≫ f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app X)
    (v ≫ g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app X))

/-- 概要：元の入力と指定全 path を Kan 引き戻しへ入れる。
方針：三座標の持ち上げ。規約：元の全円柱。使われ方：同時検出の標的射。 -/
def kanCospanPoint : K ⟶ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map f)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map g) :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackHomotopyPoint (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map g)
    (u ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app E) (v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app D)
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanCospanUnitPath f g u v H)

/-- 概要：標的射の第一入力は元の入力の単位による像。
方針：持ち上げの射影。規約：元の u。使われ方：有限比較の第一座標。 -/
lemma kanCospanPoint_left : kanCospanPoint f g u v H ≫
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map g) =
      u ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app E := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackHomotopyPoint_left _ _ _ _ _

/-- 概要：標的射の第二入力は元の入力の単位による像。
方針：持ち上げの射影。規約：元の v。使われ方：有限比較の第二座標。 -/
lemma kanCospanPoint_right : kanCospanPoint f g u v H ≫
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackRight (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map g) =
      v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app D := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackHomotopyPoint_right _ _ _ _ _

/-- 概要：標的射の全 path は指定全円柱の curry。
方針：持ち上げの射影。規約：選び直さない。使われ方：指定 path の厳密な比較。 -/
lemma kanCospanPoint_path : kanCospanPoint f g u v H ≫
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackPath (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map g) =
      curry ((β_ (Δ[1] : SSet.{u}) K).hom ≫ H.h) :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackHomotopyPoint_path _ _ _ _ _

/-- 概要：元の入力と全円柱が同じなら標的射も同じ。
方針：三座標の一意性。規約：端点の証明の選択に依存しない。使われ方：二段の比較の接続。 -/
lemma kanCospanPoint_congr
    (H' : SSet.Homotopy (u ≫ f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app X)
      (v ≫ g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app X)) (h : H.h = H'.h) :
    kanCospanPoint f g u v H = kanCospanPoint f g u v H' := by
  apply _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullback_hom_ext
  · rw [kanCospanPoint_path, kanCospanPoint_path, h]
  · rw [kanCospanPoint_left, kanCospanPoint_left]
  · rw [kanCospanPoint_right, kanCospanPoint_right]

end SerrePositivity.InfinityCategories.Project.FilteredExchange
