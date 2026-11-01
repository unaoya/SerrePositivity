module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.TwoSidedGrothendieck

/-!
# 二方向の Grothendieck 構成の係数射と底の変更

概要：左右の係数自然変換と底の関手が元の三成分の全圏へ作用する。
方針：同じ二段の Grothendieck 構成の map と pre を合成する。
規約：底・左右の対象と元の底の全射を保持する。
使われ方：DK §10.4・10.5で弱同値性を証明する実際の二つの比較関手。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.TwoSidedGrothendieck
open CategoryTheory Opposite

variable {W : Type u} [Category.{u} W]
  {F F' : Wᵒᵖ ⥤ Cat.{u, u}} {G G' : W ⥤ Cat.{u, u}}

def contravariantMap (α : F ⟶ F') : contravariantTotal F ⥤ contravariantTotal F' :=
  (Grothendieck.map (Functor.whiskerRight α Cat.opFunctor)).op

def coefficientMap (α : F ⟶ F') (β : G ⟶ G') : total F G ⥤ total F' G' :=
  Grothendieck.map (Functor.whiskerLeft (contravariantProjection F) β) ⋙
    Grothendieck.pre (contravariantProjection F' ⋙ G') (contravariantMap α)

lemma coefficientMap_obj_mk (α : F ⟶ F') (β : G ⟶ G')
    (w : W) (a : F.obj (op w)) (b : G.obj w) :
    (coefficientMap α β).obj (mk F G w a b) =
      mk F' G' w ((α.app (op w)).toFunctor.obj a) ((β.app w).toFunctor.obj b) := rfl

lemma coefficientMap_projection (α : F ⟶ F') (β : G ⟶ G') :
    coefficientMap α β ⋙ projection = projection := rfl

variable {V : Type u} [Category.{u} V] (H : V ⥤ W)

def contravariantBaseChange (F : Wᵒᵖ ⥤ Cat.{u, u}) :
    contravariantTotal (H.op ⋙ F) ⥤ contravariantTotal F :=
  (Grothendieck.pre (F ⋙ Cat.opFunctor) H.op).op

def baseChange (F : Wᵒᵖ ⥤ Cat.{u, u}) (G : W ⥤ Cat.{u, u}) :
    total (H.op ⋙ F) (H ⋙ G) ⥤ total F G :=
  Grothendieck.pre (contravariantProjection F ⋙ G) (contravariantBaseChange H F)

lemma baseChange_obj_mk (w : V) (a : F.obj (op (H.obj w))) (b : G.obj (H.obj w)) :
    (baseChange H F G).obj (mk (H.op ⋙ F) (H ⋙ G) w a b) = mk F G (H.obj w) a b := rfl

lemma baseChange_projection :
    baseChange H F G ⋙ projection = projection ⋙ H := rfl

lemma baseChange_map_homMk {w w' : V} (a : F.obj (op (H.obj w)))
    (a' : F.obj (op (H.obj w'))) (b : G.obj (H.obj w)) (b' : G.obj (H.obj w'))
    (h : w ⟶ w') (f : a ⟶ (F.map (H.map h).op).toFunctor.obj a')
    (g : (G.map (H.map h)).toFunctor.obj b ⟶ b') :
    (baseChange H F G).map (homMk (X := mk (H.op ⋙ F) (H ⋙ G) w a b)
      (Y := mk (H.op ⋙ F) (H ⋙ G) w' a' b') h f g) =
      homMk (X := mk F G (H.obj w) a b) (Y := mk F G (H.obj w') a' b') (H.map h) f g := rfl

end SerrePositivity.EInfinity.Hammock.TwoSidedGrothendieck
