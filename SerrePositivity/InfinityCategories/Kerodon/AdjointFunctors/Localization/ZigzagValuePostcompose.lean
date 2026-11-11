module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagPathIntervalValue

/-!
# 元の反転関手の後合成と zigzag の値

概要：反転関手の後に元の関手を合成して評価すると、元の値の関手像に一致する。
方針：後ろ向きの像の同型を mapIso で比較し、全射列と端点の移送を回収する。
規約：新しい逆射の選択には依存しない。
使われ方：元の通常の局所化関手の係数の自然性。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v u' v' u'' v''
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {E : Type u''} [Category.{v''} E] {W : MorphismProperty C}
  (L : C ⥤ D) (hL : W.IsInvertedBy L) (K : D ⥤ E) {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : C}

include hL in
lemma postInverts : W.IsInvertedBy (L ⋙ K) := by
  intro A B f hf
  have : IsIso (L.map f) := hL f hf
  change IsIso (K.map (L.map f))
  infer_instance

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Value.postInverts export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (postInverts)


lemma edge_postcompose (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y) (i : Fin w.length) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.edge (L ⋙ K) (postInverts L hL K) S i = K.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.edge L hL S i) := by
  cases hi : w.direction i with
  | forward =>
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.edge_forward (L ⋙ K) (postInverts L hL K) S i hi, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.edge_forward L hL S i hi]
    rfl
  | backward =>
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.edge_backward (L ⋙ K) (postInverts L hL K) S i hi, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.edge_backward L hL S i hi]
    have hh : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.backwardIso (L ⋙ K) (postInverts L hL K) S i hi =
        K.mapIso (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.backwardIso L hL S i hi) := by
      apply Iso.ext
      rfl
    exact congrArg Iso.inv hh

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Value.edge_postcompose export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (edge_postcompose)


lemma path_postcompose (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.path (L ⋙ K) (postInverts L hL K) S = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.path L hL S ⋙ K := by
  apply ComposableArrows.ext (F := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.path (L ⋙ K) (postInverts L hL K) S)
    (G := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.path L hL S ⋙ K) (fun _ => rfl)
  intro i hi
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.path (L ⋙ K) (postInverts L hL K) S).map' i (i + 1) =
    K.map ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.path L hL S).map' i (i + 1))
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.path]
  rw [ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ i hi,
    ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ i hi]
  exact edge_postcompose L hL K S ⟨i, hi⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Value.path_postcompose export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (path_postcompose)


lemma value_postcompose (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.value (L ⋙ K) (postInverts L hL K) S = K.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.value L hL S) := by
  have h := CategoryTheory.Functor.hcongr_hom (path_postcompose L hL K S)
    (homOfLE (show (0 : Fin (w.length + 1)) ≤ Fin.last _ from Fin.zero_le _))
  apply eq_of_heq
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.value]
  simp only [CategoryTheory.Functor.map_comp, eqToHom_map, eqToHom_comp_heq_iff,
    comp_eqToHom_heq_iff, heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
  exact h

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Value.value_postcompose export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (value_postcompose)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
