module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagBoundaryHom

/-!
# 元の動く接合点の縦射の恒等と合成

概要：元の接合点の射を固定 Hom と元の一列の評価へ回収する。
方針：全列の正方形と元の端点移送を保つ。
規約：接合点の縦射を恒等射とは仮定しない。
使われ方：DK9.4・10.3の元の語の Grothendieck 分解。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagBoundaryHomLaws
open CategoryTheory
variable {C : Type u} [Category.{u} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction} {X X' X'' Y : C}
  {S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons d w) X Y} {T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons d w) X' Y}
  {U : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons d w) X'' Y}
  {f : X ⟶ X'} {g : X' ⟶ X''}
def ofMoving (h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom S T) (hf : HEq (h.app 0) f)
    (hl : HEq (h.app (Fin.last (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons d w).length)) (𝟙 Y)) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BoundaryHom f S T where
  hom := h
  first := (conj_eqToHom_iff_heq _ _ S.first T.first).mpr hf
  last := h.last_of_heq_id hl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BoundaryHom export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagBoundaryHomLaws (ofMoving)


def id (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons d w) X Y) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BoundaryHom (𝟙 X) S S :=
  ofMoving (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.id S) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.id_first S) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.id_last S)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BoundaryHom export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagBoundaryHomLaws (id)


def comp (h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BoundaryHom f S T) (k : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BoundaryHom g T U) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BoundaryHom (f ≫ g) S U where
  hom := h.hom.comp k.hom
  first := by
    change h.hom.app 0 ≫ k.hom.app 0 = _
    simp only [h.first, k.first, Category.assoc, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp]
  last := by
    change h.hom.app _ ≫ k.hom.app _ = _
    simp only [h.last, k.last, eqToHom_trans]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BoundaryHom export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagBoundaryHomLaws (comp)


lemma id_app (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons d w) X Y)
    (j : Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons d w).length + 1)) : (id S).hom.app j = 𝟙 _ := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BoundaryHom export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagBoundaryHomLaws (id_app)

lemma comp_app (h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BoundaryHom f S T) (k : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BoundaryHom g T U)
    (j : Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons d w).length + 1)) :
    (comp h k).hom.app j = h.hom.app j ≫ k.hom.app j := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BoundaryHom export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagBoundaryHomLaws (comp_app)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagBoundaryHomLaws
