module

public import SerrePositivity.EInfinity.BarrattEccles.MappingSpaceHammockGraph
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentUnits

/-!
# 元の E 代数の hammock graph の語の写像による遷移

概要：任意の可換環上の実際の弱同値を使い、語の写像に対応する graph の射を構成。
方針：全縦弱同値を保持する列の圧縮関手の nerve を使う。
規約：graph 間の遷移の構成であり、語の射の合成則と全図式は後続。
使われ方：同じ E 代数の hammock の語の図式への代入。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory _root_.HomotopicalAlgebra

namespace SerrePositivity.EInfinity.BarrattEccles

variable (A : Type u) [CommRing A]

/-- 同じ実際の E 代数の固定語の zigzag 圏。 -/
abbrev algebraHammockZigzag (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y : (operad A).Algebra) :=
  let := modelCategory A
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences (operad A).Algebra) w X Y

/-- 同じ局所的に選んだモデル構造の弱同値の乗法性による、実際の zigzag の圏。 -/
instance algebraHammockZigzagCategory (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y : (operad A).Algebra) :
    Category.{u} (algebraHammockZigzag A w X Y) := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.zigzagCategory

/-- 同じ全頂点の切断と列の合成による、元の zigzag 圏間の遷移。 -/
def algebraHammockTransition {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b)
    (X Y : (operad A).Algebra) :
    algebraHammockZigzag A a X Y ⥤ algebraHammockZigzag A b X Y := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f

/-- 同じ遷移の元の nerve の射。 -/
def algebraHammockGraphMap {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b)
    (X Y : (operad A).Algebra) : algebraHammockGraph A a X Y ⟶ algebraHammockGraph A b X Y :=
  nerveMap (algebraHammockTransition A f X Y)

/-- 全頂点で、元の切断位置の対象をそのまま回収する。 -/
lemma algebraHammockTransition_vertex {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b)
    (X Y : (operad A).Algebra) (S : algebraHammockZigzag A a X Y)
    (j : Fin (b.length + 1)) :
    ((algebraHammockTransition A f X Y).obj S).vertex j = S.vertex (f.cut j) := rfl

/-- 全縦射で、元の切断位置の射をそのまま回収する。 -/
lemma algebraHammockTransition_app {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b)
    (X Y : (operad A).Algebra) {S T : algebraHammockZigzag A a X Y} (g : S ⟶ T)
    (j : Fin (b.length + 1)) :
    ((algebraHammockTransition A f X Y).map g).app j = g.app (f.cut j) := rfl

end SerrePositivity.EInfinity.BarrattEccles
