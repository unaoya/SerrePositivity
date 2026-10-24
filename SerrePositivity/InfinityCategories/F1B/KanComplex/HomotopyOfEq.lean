module

public import SerrePositivity.InfinityCategories.F1B.Homotopy.HomotopyWhiskering

/-!
概要：射の等式を定値な指定ホモトピーとして表す。
方針：終点の定値円柱を使い、始点の証明だけを等式で輸送する。
規約：円柱自体は終点の射による定値な後合成。
使われ方：像の類が恒等である相対 Kan 単位の代表修正。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：二関手の等式を終点で定値な指定ホモトピーとして表す。
方針：恒等ホモトピーの始点の証明を等式で戻す。
規約：元の二関手の表示は変えない。
使われ方：底での厳密な等式に付随する単位の代表。 -/
def kanHomotopyOfEq {K E : SSet.{u}} {f g : K ⟶ E} (h : f = g) :
    SSet.Homotopy f g where
  h := (functorHomotopyRefl g).h
  h₀ := (functorHomotopyRefl g).h₀.trans h.symm
  h₁ := (functorHomotopyRefl g).h₁
  rel := (functorHomotopyRefl g).rel

/-- 概要：等式の指定ホモトピーが表す射は等式による輸送。
方針：等式を消去し、恒等ホモトピーの類の公式を使う。
規約：同じ宇宙の h Fun の射として述べる。
使われ方：像の類が恒等という入力を像の代表の等式へ渡す。 -/
lemma kanHomotopyOfEq_hom {K E : SSet.{u}} {f g : K ⟶ E} (h : f = g) :
    SSet.Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (kanHomotopyOfEq h)) =
        eqToHom (congrArg (fun q : K ⟶ E ↦ HomotopyCategory.mk (functorVertex q)) h) := by
  subst g
  exact functorHomotopyRefl_hom f

end SerrePositivity.InfinityCategories.F1B
