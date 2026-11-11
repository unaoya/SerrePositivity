module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieckHomComponents

/-!
# 元の反変 Grothendieck 全圏の底と fiber の射の回収

概要：反変全圏の射を元の底の射と逆変の fiber の射で判定する。
方針：元の Grothendieck の二つの成分を反転して回収する。
規約：元の全射を保持し、端点移送は異種等式で吸収する。
使われ方：DK9.5の右ラベル次数を固定した左比較の関手則。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ContravariantGrothendieckComponents
open CategoryTheory Opposite
open TwoSidedGrothendieck

variable {W : Type u} [Category.{u} W] {F : Wᵒᵖ ⥤ Cat.{u, u}}

def base (X : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.contravariantTotal F) : W := X.unop.base.unop

def fiber (X : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.contravariantTotal F) : F.obj (op (base X)) := X.unop.fiber.unop

def baseMap {X Y : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.contravariantTotal F} (f : X ⟶ Y) : base X ⟶ base Y := f.unop.base.unop

def fiberMap {X Y : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.contravariantTotal F} (f : X ⟶ Y) :
    fiber X ⟶ (F.map (baseMap f).op).toFunctor.obj (fiber Y) := f.unop.fiber.unop

def homMk {X Y : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.contravariantTotal F} (h : base X ⟶ base Y)
    (f : fiber X ⟶ (F.map h.op).toFunctor.obj (fiber Y)) : X ⟶ Y :=
  Quiver.Hom.op (show Y.unop ⟶ X.unop from ⟨h.op, f.op⟩)

def homEquiv (X Y : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.contravariantTotal F) : (X ⟶ Y) ≃
    (Σ h : base X ⟶ base Y, fiber X ⟶ (F.map h.op).toFunctor.obj (fiber Y)) where
  toFun f := ⟨baseMap f, fiberMap f⟩
  invFun f := homMk f.1 f.2
  left_inv _ := rfl
  right_inv _ := rfl

lemma hom_ext_heq {X Y : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.contravariantTotal F} (f g : X ⟶ Y) (hb : baseMap f = baseMap g)
    (hf : HEq (fiberMap f) (fiberMap g)) : f = g :=
  (homEquiv X Y).injective (Sigma.ext hb hf)

lemma fiberMap_id_heq (X : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.contravariantTotal F) : HEq (fiberMap (𝟙 X)) (𝟙 (fiber X)) := by
  have h := congrArg Quiver.Hom.unop (Grothendieck.id_fiber X.unop)
  exact (heq_of_eq h).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieckHomComponents.unop_eqToHom_heq_id _)

lemma fiberMap_comp_heq {X Y Z : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.contravariantTotal F} (f : X ⟶ Y) (g : Y ⟶ Z) :
    HEq (fiberMap (f ≫ g))
      (fiberMap f ≫ (F.map (baseMap f).op).toFunctor.map (fiberMap g)) := by
  have h := congrArg Quiver.Hom.unop (Grothendieck.comp_fiber g.unop f.unop)
  exact (heq_of_eq h).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieckHomComponents.unop_eqToHom_comp_heq _ _ _)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ContravariantGrothendieckComponents
