module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagPathIntervalValue

/-!
# 元の反転関手の後合成と zigzag の値

概要：反転関手の後に元の関手を合成して評価すると、元の値の関手像に一致する。
方針：後ろ向きの像の同型を mapIso で比較し、全射列と端点の移送を回収する。
規約：新しい逆射の選択には依存しない。
使われ方：元の通常の局所化関手の係数の自然性。
-/

@[expose] public section
universe u v u' v' u'' v''
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.Zigzag.Value
open CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {E : Type u''} [Category.{v''} E] {W : MorphismProperty C}
  (L : C ⥤ D) (hL : W.IsInvertedBy L) (K : D ⥤ E) {w : Word} {X Y : C}

include hL in
lemma postInverts : W.IsInvertedBy (L ⋙ K) := by
  intro A B f hf
  have : IsIso (L.map f) := hL f hf
  change IsIso (K.map (L.map f))
  infer_instance

lemma edge_postcompose (S : Zigzag W w X Y) (i : Fin w.length) :
    edge (L ⋙ K) (postInverts L hL K) S i = K.map (edge L hL S i) := by
  cases hi : w.direction i with
  | forward =>
    rw [edge_forward (L ⋙ K) (postInverts L hL K) S i hi, edge_forward L hL S i hi]
    rfl
  | backward =>
    rw [edge_backward (L ⋙ K) (postInverts L hL K) S i hi, edge_backward L hL S i hi]
    have hh : backwardIso (L ⋙ K) (postInverts L hL K) S i hi =
        K.mapIso (backwardIso L hL S i hi) := by
      apply Iso.ext
      rfl
    exact congrArg Iso.inv hh

lemma path_postcompose (S : Zigzag W w X Y) :
    path (L ⋙ K) (postInverts L hL K) S = path L hL S ⋙ K := by
  apply ComposableArrows.ext (F := path (L ⋙ K) (postInverts L hL K) S)
    (G := path L hL S ⋙ K) (fun _ => rfl)
  intro i hi
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change (path (L ⋙ K) (postInverts L hL K) S).map' i (i + 1) =
    K.map ((path L hL S).map' i (i + 1))
  dsimp only [path]
  rw [ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ i hi,
    ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ i hi]
  exact edge_postcompose L hL K S ⟨i, hi⟩

lemma value_postcompose (S : Zigzag W w X Y) :
    value (L ⋙ K) (postInverts L hL K) S = K.map (value L hL S) := by
  have h := CategoryTheory.Functor.hcongr_hom (path_postcompose L hL K S)
    (homOfLE (show (0 : Fin (w.length + 1)) ≤ Fin.last _ from Fin.zero_le _))
  apply eq_of_heq
  dsimp only [value]
  simp only [CategoryTheory.Functor.map_comp, eqToHom_map, eqToHom_comp_heq_iff,
    comp_eqToHom_heq_iff, heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
  exact h

end SerrePositivity.EInfinity.Hammock.Zigzag.Value
