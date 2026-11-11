module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieckFunctoriality

/-!
# 二方向の Grothendieck 構成の左右交換

概要：底と両係数を反転して左右を交換すると元の全圏の反対圏を得る。
方針：元の底・左・右の三成分を交換し、全射の三成分も交換する。
規約：単なる対象の対応だけでなく元の全圏の関手を構成する。
使われ方：DK §9.6の左係数の不変性を右係数の定理へ帰着する。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory Opposite

lemma unopUnop_eqToHom {D : Type u} [Category.{u} D] {A B : Dᵒᵖᵒᵖ} (h : A = B) :
    (eqToHom h).unop.unop = eqToHom (congrArg (fun Z => Z.unop.unop) h) := by
  cases h
  rfl

lemma unopUnop_eqToHom_comp_heq {D : Type u} [Category.{u} D]
    {A A' B E : Dᵒᵖᵒᵖ} (h : A' = A) (f : A ⟶ B) (g : B ⟶ E) :
    HEq ((eqToHom h ≫ f ≫ g).unop.unop) (f ≫ g).unop.unop := by
  cases h
  simp

variable {W : Type u} [Category.{u} W] (F : Wᵒᵖ ⥤ Cat.{u, u}) (G : W ⥤ Cat.{u, u})

def dualLeft : Wᵒᵖᵒᵖ ⥤ Cat.{u, u} := (opOpEquivalence W).functor ⋙ G ⋙ Cat.opFunctor

def dualRight : Wᵒᵖ ⥤ Cat.{u, u} := F ⋙ Cat.opFunctor

def dualObj (X : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.total F G) : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.total (dualLeft G) (dualRight F))ᵒᵖ :=
  op (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.mk (dualLeft G) (dualRight F) (op (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.base F G X)) (op (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.right F G X)) (op (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.left F G X)))

def dualMap {X Y : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.total F G} (f : X ⟶ Y) : dualObj F G X ⟶ dualObj F G Y :=
  Quiver.Hom.op (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.homMk (X := (dualObj F G Y).unop) (Y := (dualObj F G X).unop)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.baseMap f).op (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.rightMap f).op (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.leftMap f).op)

def dualFunctor : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.total F G ⥤ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.total (dualLeft G) (dualRight F))ᵒᵖ where
  obj := dualObj F G
  map := dualMap F G
  map_id X := by
    apply Quiver.Hom.unop_inj
    refine Grothendieck.ext _ _ ?_ ?_
    · apply Quiver.Hom.unop_inj
      refine Grothendieck.ext _ _ ?_ ?_
      · rfl
      · simp [dualMap, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.homMk, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.leftMap, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.rightMap, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.baseMap,
          _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.contravariantProjection, dualLeft, dualRight]
    · simp [dualMap, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.homMk, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.leftMap, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.rightMap, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.baseMap,
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.contravariantProjection, dualLeft, dualRight]
  map_comp f g := by
    apply Quiver.Hom.unop_inj
    refine Grothendieck.ext _ _ ?_ ?_
    · apply Quiver.Hom.unop_inj
      refine Grothendieck.ext _ _ ?_ ?_
      · rfl
      · simp [dualMap, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.homMk, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.leftMap, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.rightMap, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.baseMap,
          _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.contravariantProjection, dualLeft, dualRight]
        rfl
    · simp [dualMap, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.homMk, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.leftMap, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.rightMap, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.baseMap,
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.contravariantProjection, dualLeft, dualRight]
      rfl

def unDualObj (X : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.total (dualLeft G) (dualRight F))ᵒᵖ) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.total F G :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.mk F G (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.base (dualLeft G) (dualRight F) X.unop).unop
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.right (dualLeft G) (dualRight F) X.unop).unop
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.left (dualLeft G) (dualRight F) X.unop).unop

def unDualMap {X Y : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.total (dualLeft G) (dualRight F))ᵒᵖ} (f : X ⟶ Y) :
    unDualObj F G X ⟶ unDualObj F G Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.baseMap f.unop).unop (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.rightMap f.unop).unop (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.leftMap f.unop).unop

def unDualFunctor : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.total (dualLeft G) (dualRight F))ᵒᵖ ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.total F G where
  obj := unDualObj F G
  map := unDualMap F G
  map_id X := by
    refine Grothendieck.ext _ _ ?_ ?_
    · apply Quiver.Hom.unop_inj
      refine Grothendieck.ext _ _ ?_ ?_
      · rfl
      · simp [unDualMap, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.homMk, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.leftMap, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.rightMap, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.baseMap,
          _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.contravariantProjection, dualLeft, dualRight]
    · dsimp only [unDualMap, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.homMk, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.leftMap, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.rightMap, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.baseMap,
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.contravariantProjection, dualLeft, dualRight]
      simp only [Functor.comp_obj, Grothendieck.id_base, Functor.comp_map, eqToHom_refl,
        Category.id_comp, Grothendieck.id_fiber, unop_id]
      exact unopUnop_eqToHom _
  map_comp f g := by
    refine Grothendieck.ext _ _ ?_ ?_
    · apply Quiver.Hom.unop_inj
      refine Grothendieck.ext _ _ ?_ ?_
      · rfl
      · simp [unDualMap, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.homMk, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.leftMap, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.rightMap, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.baseMap,
          _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.contravariantProjection, dualLeft, dualRight]
        rfl
    · dsimp only [unDualMap, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.homMk, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.leftMap, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.rightMap, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.baseMap,
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.contravariantProjection, dualLeft, dualRight]
      simp only [Functor.comp_obj, Grothendieck.comp_base, Functor.comp_map, eqToHom_refl,
        Category.id_comp, Grothendieck.comp_fiber]
      apply eq_of_heq
      refine (unopUnop_eqToHom_comp_heq _ _ _).trans ?_
      simp only [heq_eqToHom_comp_iff]
      rfl

def dualEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.total F G ≌ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.total (dualLeft G) (dualRight F))ᵒᵖ where
  functor := dualFunctor F G
  inverse := unDualFunctor F G
  unitIso := Iso.refl _
  counitIso := Iso.refl _

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
