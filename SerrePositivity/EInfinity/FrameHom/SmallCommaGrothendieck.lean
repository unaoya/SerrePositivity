module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CommaGrothendieck
public import SerrePositivity.EInfinity.FrameHom.NerveAsSmall
public import SerrePositivity.EInfinity.FrameHom.NerveEquivalenceImage

/-!
# 小さい全図式から元の comma への明示的な回収

概要：対象・射の宇宙を揃えた両関手の全図式から、元の両関手の comma を回収する。
方針：元の対象・中間射・左右の射を down し、同じデータの up を逆に使う。
規約：出力も AsSmall で同じ宇宙に揃える。元の中間射を保持する。
使われ方：元の Map^h の小さい全図式から元の三本矢の nerve への接続。
-/

@[expose] public section
universe u v w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.EInfinity.FrameHom.SmallCommaGrothendieck
open SerrePositivity.SimplicialModel

variable {K J C : Type u} [Category.{v} K] [Category.{v} J] [Category.{v} C]
  (Q : K ⥤ C) (R : J ⥤ C)

/-- 元の関手の前後で対象と射の宇宙だけを揃える。 -/
abbrev smallFunctor (F : K ⥤ C) : AsSmall.{w} K ⥤ AsSmall.{w} C :=
  AsSmall.down ⋙ F ⋙ AsSmall.up

/-- 元の右対象・左対象・中間射を持ち上げた全図式。 -/
abbrev diagram := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CommaGrothendieck.diagram (smallFunctor.{u, v, w} Q) (smallFunctor R)

/-- 同じ小さい comma のデータを down し、元の comma の小圏へ送る。 -/
def commaDown : Comma (smallFunctor.{u, v, w} Q) (smallFunctor R) ⥤
    AsSmall.{w} (Comma Q R) where
  obj S := AsSmall.up.obj ⟨AsSmall.down.obj S.left, AsSmall.down.obj S.right, S.hom.down⟩
  map f := AsSmall.up.map ⟨f.left.down, f.right.down, congrArg ULift.down f.w⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- 元の comma の同じデータを up して小さい両関手の comma へ戻す。 -/
def commaUp : AsSmall.{w} (Comma Q R) ⥤
    Comma (smallFunctor.{u, v, w} Q) (smallFunctor R) where
  obj S := ⟨AsSmall.up.obj (AsSmall.down.obj S).left,
    AsSmall.up.obj (AsSmall.down.obj S).right, AsSmall.up.map (AsSmall.down.obj S).hom⟩
  map f := ⟨AsSmall.up.map f.down.left, AsSmall.up.map f.down.right, by
    apply ULift.ext
    exact f.down.w⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- 小さい comma の元の対象と射は厳密に戻る。 -/
lemma commaDown_commaUp : commaDown.{u, v, w} Q R ⋙ commaUp Q R = 𝟭 _ := rfl

/-- 元の comma の up/down も全対象・全射で厳密に戻る。 -/
lemma commaUp_commaDown : commaUp.{u, v, w} Q R ⋙ commaDown Q R = 𝟭 _ := rfl

/-- 同じ両関手の comma の宇宙比較の明示的な同値。 -/
def commaEquivalence : Comma (smallFunctor.{u, v, w} Q) (smallFunctor R) ≌
    AsSmall.{w} (Comma Q R) :=
  CategoryTheory.Equivalence.mk (commaDown Q R) (commaUp Q R)
    (eqToIso (commaDown_commaUp Q R).symm) (eqToIso (commaUp_commaDown Q R))

/-- 同じ小さい全図式から、元の comma の小圏への回収の同値。 -/
def equivalence : Grothendieck (diagram.{u, v, w} Q R) ≌ AsSmall.{w} (Comma Q R) :=
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CommaGrothendieck.equivalence (smallFunctor Q) (smallFunctor R)).trans (commaEquivalence Q R)

/-- 元の全図式の nerve から元の comma の nerve の宇宙拡大への同じ回収。 -/
def recoveryNerveMap : nerve (Grothendieck (diagram.{u, v, w} Q R)) ⟶
    SSet.uliftFunctor.{w, max u v}.obj (nerve (Comma Q R)) :=
  nerveMap (equivalence Q R).functor ≫ (NerveAsSmall.iso (Comma Q R)).hom

/-- 同じ元の全図式の回収射そのものは局所化で可逆。 -/
lemma recoveryNerveMap_localized_isIso :
    IsIso (AnodyneHomotopy.anodyneQ.map (recoveryNerveMap.{u, v, w} Q R)) := by
  have : IsIso (AnodyneHomotopy.anodyneQ.map (nerveMap (equivalence.{u, v, w} Q R).functor)) :=
    (NerveEquivalenceImage.imageIso (equivalence.{u, v, w} Q R) AnodyneHomotopy.anodyneQ
      (Localization.inverts _ SSet.anodyneExtensions)).isIso_hom
  dsimp only [recoveryNerveMap]
  rw [CategoryTheory.Functor.map_comp]
  infer_instance

end SerrePositivity.EInfinity.FrameHom.SmallCommaGrothendieck
