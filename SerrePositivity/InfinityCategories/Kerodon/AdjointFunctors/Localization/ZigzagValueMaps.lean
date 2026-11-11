module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath

/-!
# 元の全縦射による zigzag の値の不変性

概要：元の全縦射は値の射列の自然変換を与え、両端固定なら元の値を保つ。
方針：後ろ向きの列の可換正方形を反転し、全射列と端点の等式を回収する。
規約：全縦射を保持する。対象のモデル構造や局所化の飽和性は要求しない。
使われ方：各 hammock graph から通常の局所化 Hom の定数単体集合への評価。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {W : MorphismProperty C} [W.IsMultiplicative] (L : C ⥤ D) (hL : W.IsInvertedBy L)
  {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : C} {S T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y}

lemma edge_comm (f : S ⟶ T) (i : Fin w.length) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.edge L hL S i ≫ L.map (f.app i.succ) = L.map (f.app i.castSucc) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.edge L hL T i := by
  cases hi : w.direction i with
  | forward =>
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.edge_forward L hL S i hi, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.edge_forward L hL T i hi,
      ← L.map_comp, ← L.map_comp]
    exact congrArg L.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentNaturality.forward_arrow_comm f i hi)
  | backward =>
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.edge_backward L hL S i hi, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.edge_backward L hL T i hi]
    have hc : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.backwardIso L hL S i hi).hom ≫ L.map (f.app i.castSucc) =
        L.map (f.app i.succ) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.backwardIso L hL T i hi).hom := by
      change L.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow .backward S i hi).unop ≫ L.map (f.app i.castSucc) =
        L.map (f.app i.succ) ≫ L.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow .backward T i hi).unop
      rw [← L.map_comp, ← L.map_comp]
      exact congrArg L.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentNaturality.backward_arrow_comm f i hi)
    apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.backwardIso L hL S i hi).hom).1
    rw [Iso.hom_inv_id_assoc, ← Category.assoc, hc, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Value.edge_comm export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (edge_comm)


def pathMap (f : S ⟶ T) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.path L hL S ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.path L hL T :=
  ComposableArrows.homMk (fun j => L.map (f.app j)) (by
    intro i hi
    dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.path]
    rw [ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ i hi,
      ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ i hi]
    exact edge_comm L hL f ⟨i, hi⟩)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Value.pathMap export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (pathMap)


lemma value_eq (f : S ⟶ T) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.value L hL S = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.value L hL T := by
  have hc := (pathMap L hL f).naturality
    (homOfLE (show (0 : Fin (w.length + 1)) ≤ Fin.last _ from Fin.zero_le _))
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.path L hL S).hom ≫ L.map (f.app (Fin.last w.length)) =
    L.map (f.app 0) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.path L hL T).hom at hc
  rw [f.last, f.first, eqToHom_map, eqToHom_map] at hc
  have h := congrArg (fun k => eqToHom (congrArg L.obj S.first.symm) ≫ k ≫
    eqToHom (congrArg L.obj T.last)) hc
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.value, Category.assoc, eqToHom_trans, eqToHom_trans_assoc] using h

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Value.value_eq export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (value_eq)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
