module

public import SerrePositivity.KST.ProExcision.ActionCategory
public import SerrePositivity.KST.ProExcision.SimplicialAction

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# 単体的作用の圏の二重 nerve

概要：次数ごとのモノイド作用の圏を単体的圏として組み立て、二重 nerve と対角を取る。
方針：全単体射に作用圏の同変な誘導関手を使う。
規約：G の正則作用に限らない。群状性はまだ要求しない。
使われ方：KST Appendix A の E_X G の具体模型、Prop A.1 の作用 bar の構成。
-/

universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open SerrePositivity.KST.Comparison
variable {G H : SimplicialObject MonCat.{u}}

/-- 概要：単体的モノイド作用の次数ごとの作用の圏。
方針：各単体射で、モノイド成分と作用先の成分を同時に写す。
規約：圏の対象は作用先 H の元、射のラベルは G の元。
使われ方：KST App. A の作用 bar の全ての面・退化の構成。 -/
def simplicialActionCategory (A : SimplicialMonoidAction G H) : SimplicialObject Cat.{u, u} where
  obj n := letI := A.actionStructure n; Cat.of (ActionObject (G.obj n) (H.obj n))
  map {n m} f := by
    letI := A.actionStructure n
    letI := A.actionStructure m
    exact (actionCategoryMap (G.map f).hom (H.map f).hom (A.naturality f)).toCatHom
  map_id n := by
    letI := A.actionStructure n
    change (actionCategoryMap (G.map (𝟙 n)).hom (H.map (𝟙 n)).hom _).toCatHom = _
    simp only [G.map_id, H.map_id]
    rfl
  map_comp {n m k} f g := by
    letI := A.actionStructure n
    letI := A.actionStructure m
    letI := A.actionStructure k
    change (actionCategoryMap (G.map (f ≫ g)).hom (H.map (f ≫ g)).hom _).toCatHom = _
    simp only [G.map_comp, H.map_comp]
    rfl

/-- 概要：単体的モノイド作用の圏の二重単体的 nerve。
方針：次数ごとの作用の圏へ nerve 関手を合成する。
規約：二つの単体方向を保持する。使われ方：KST Appendix A の E_X G の二重模型。 -/
def bisimplicialActionBar (A : SimplicialMonoidAction G H) : SimplicialObject SSet.{u} :=
  simplicialActionCategory A ⋙ nerveFunctor

/-- 概要：作用の圏の二重 nerve の対角。
方針：二つの単体添字を対角に制限する。
規約：群状性なしに定義される。使われ方：KST Appendix A の E_X G。 -/
def actionBar (A : SimplicialMonoidAction G H) : SSet.{u} :=
  Functor.diag SimplexCategoryᵒᵖ ⋙ Functor.uncurry.obj (bisimplicialActionBar A)

end SerrePositivity.KST.ProExcision
