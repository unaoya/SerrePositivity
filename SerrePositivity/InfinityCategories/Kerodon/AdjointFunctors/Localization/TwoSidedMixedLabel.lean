module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieckFunctoriality
public import Mathlib.CategoryTheory.Elements

/-!
# 右ラベルを固定した元の混合全圏と反対 Grothendieck 全圏

概要：元の反変全圏に右ラベルを付けた要素圏を、右ラベルの要素圏上の反対全圏へ移す。
方針：元の底・左対象・右ラベルと全射をそのまま並べ替える。
規約：元のラベルの条件を保持し、新しい代表や逆像の選択を使わない。
使われ方：DK9.5の元の比較の各右ラベル次数の弱同値性。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedMixedLabel
open CategoryTheory Opposite TwoSidedGrothendieck

variable {W : Type u} [Category.{u} W] (F : Wᵒᵖ ⥤ Cat.{u, u}) (S : W ⥤ Type u)

abbrev mixed := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.contravariantProjection F ⋙ S).Elements

abbrev pulledDiagram : S.Elementsᵒᵖ ⥤ Cat.{u, u} :=
  (Functor.Elements.π S).op ⋙ F ⋙ Cat.opFunctor

abbrev pulledTotal := (Grothendieck (pulledDiagram F S))ᵒᵖ

def toMixed : pulledTotal F S ⥤ mixed F S where
  obj X := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.contravariantProjection F ⋙ S).elementsMk
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieckFunctoriality.contravariantBaseChange (Functor.Elements.π S) F).obj X) X.unop.base.unop.val
  map f := Functor.Elements.homMk
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieckFunctoriality.contravariantBaseChange (Functor.Elements.π S) F).map f) f.unop.base.unop.map_val
  map_id X := Functor.Elements.hom_ext
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieckFunctoriality.contravariantBaseChange (Functor.Elements.π S) F).map_id X)
  map_comp f g := Functor.Elements.hom_ext
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieckFunctoriality.contravariantBaseChange (Functor.Elements.π S) F).map_comp f g)

def fromMixedObj (X : mixed F S) : pulledTotal F S :=
  op ⟨op (S.elementsMk X.obj.unop.base.unop X.val), X.obj.unop.fiber⟩

def fromMixedMap {X Y : mixed F S} (f : X ⟶ Y) : fromMixedObj F S X ⟶ fromMixedObj F S Y :=
  Quiver.Hom.op (show (fromMixedObj F S Y).unop ⟶ (fromMixedObj F S X).unop from
    { base := Quiver.Hom.op
        (show (fromMixedObj F S X).unop.base.unop ⟶ (fromMixedObj F S Y).unop.base.unop from
          Functor.Elements.homMk f.hom.unop.base.unop f.map_val)
      fiber := f.hom.unop.fiber })

lemma toMixed_map_fromMixedMap {X Y : mixed F S} (f : X ⟶ Y) :
    (toMixed F S).map (fromMixedMap F S f) = f := rfl

lemma fromMixedMap_toMixed_map {X Y : pulledTotal F S} (f : X ⟶ Y) :
    fromMixedMap F S ((toMixed F S).map f) = f := rfl

lemma toMixed_map_injective {X Y : pulledTotal F S} {f g : X ⟶ Y}
    (h : (toMixed F S).map f = (toMixed F S).map g) : f = g :=
  congrArg (fromMixedMap F S) h

def fromMixed : mixed F S ⥤ pulledTotal F S where
  obj := fromMixedObj F S
  map := fromMixedMap F S
  map_id X := by
    apply toMixed_map_injective F S
    rw [(toMixed F S).map_id]
    rfl
  map_comp f g := by
    apply toMixed_map_injective F S
    rw [(toMixed F S).map_comp]
    rfl

def equivalence : pulledTotal F S ≌ mixed F S where
  functor := toMixed F S
  inverse := fromMixed F S
  unitIso := Iso.refl _
  counitIso := Iso.refl _

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedMixedLabel
