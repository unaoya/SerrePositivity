module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionOnePointDegeneracy

/-!
概要：終頂点が一点の非退化な実全単体には最初の二点を併合する隣接辺が存在する。
方針：併合がなければ各実射が0の逆像を反映することを尾部から帰納する。
規約：位置や辺の存在を仮定に追加しない。
使われ方：Riehl–Verity §4.1–§4.2の原子の最初の併合の選択、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実親の構成。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：指定した隣接辺が二番目の点を0へ送る条件。
方針：元の実射の共通表示の実点を記録する。規約：二点あることも証人から従う。
使われ方：Riehl–Verity §4.1の最初の併合位置。 -/
def WalkingAdjunctionBottomMergeAt {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : Fin (n + 2) ⥤ walkingAdjunctionHom .minus Y) (k : Fin (n + 1)) : Prop :=
  ∃ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)), i.val = 1 ∧
    (walkingAdjunctionOrderHom (H.map (homOfLE (Fin.castSucc_le_succ k))) i).val = 0

/-- 概要：二番目の点を0へ送らない有限単調射は0の逆像を反映する。
方針：正の点の下にある値1の点で単調性を使う。規約：空の有限順序も含む。
使われ方：Riehl–Verity §4.1の隣接辺から全尾部への帰納。 -/
lemma ordinalReflectsZero_of_no_one {m n : ℕ} (f : Fin m →o Fin n)
    (h : ∀ j : Fin m, j.val = 1 → (f j).val ≠ 0) :
    ∀ i : Fin m, (f i).val = 0 → i.val = 0 := by
  intro i hi
  by_contra hn
  have hp : 0 < i.val := by omega
  let j : Fin m := ⟨1, by have hm := i.isLt; omega⟩
  have hj := h j rfl
  have hm := f.monotone (show j ≤ i from by change 1 ≤ i.val; omega)
  change (f j).val ≤ (f i).val at hm
  omega

/-- 概要：終頂点が一点で全隣接辺に併合がなければ全頂点が一点。
方針：尾部の全射が0を反映することを逆帰納し、二番目の点の存在を排除する。
規約：元の実関手の全合成則を使う。使われ方：Riehl–Verity §4.1の位置の存在の証明。 -/
lemma walkingAdjunctionCard_one_of_no_bottom_merge {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : Fin (n + 2) ⥤ walkingAdjunctionHom .minus Y)
    (hlast : walkingAdjunctionOrdinalCard .minus Y (H.obj (Fin.last (n + 1))) = 1)
    (hno : ∀ k, ¬ WalkingAdjunctionBottomMergeAt H k) :
    ∀ i, walkingAdjunctionOrdinalCard .minus Y (H.obj i) = 1 := by
  have hR (i : Fin (n + 2)) : ∀ a : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj i)),
      (walkingAdjunctionOrderHom (H.map (homOfLE (Fin.le_last i))) a).val = 0 → a.val = 0 := by
    induction i using Fin.reverseInduction with
    | last =>
      intro a ha
      have he : homOfLE (Fin.le_last (Fin.last (n + 1))) = 𝟙 (Fin.last (n + 1)) :=
        Subsingleton.elim _ _
      rw [he, H.map_id, walkingAdjunctionOrderHom_id] at ha
      exact ha
    | cast k ih =>
      intro a ha
      let f := H.map (homOfLE (Fin.castSucc_le_succ k))
      let b := walkingAdjunctionOrderHom f a
      have he : H.map (homOfLE (Fin.le_last k.castSucc)) =
          f ≫ H.map (homOfLE (Fin.le_last k.succ)) := by
        rw [← H.map_comp]
        rfl
      have hz : (walkingAdjunctionOrderHom (H.map (homOfLE (Fin.le_last k.succ))) b).val = 0 := by
        rw [he, walkingAdjunctionOrderHom_comp] at ha
        exact ha
      have hb : b.val = 0 := ih b hz
      exact ordinalReflectsZero_of_no_one (walkingAdjunctionOrderHom f)
        (fun j hj hz => hno k ⟨j, hj, hz⟩) a hb
  intro i
  have hp := NeZero.pos (walkingAdjunctionOrdinalCard .minus Y (H.obj i))
  by_contra hn
  have hi : 1 < walkingAdjunctionOrdinalCard .minus Y (H.obj i) := by omega
  let a : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj i)) := ⟨1, hi⟩
  have hz : (walkingAdjunctionOrderHom (H.map (homOfLE (Fin.le_last i))) a).val = 0 := by
    have ha := (walkingAdjunctionOrderHom (H.map (homOfLE (Fin.le_last i))) a).isLt
    omega
  have he := hR i a hz
  change 1 = 0 at he
  omega

/-- 概要：終頂点が一点の正の次元の非退化な全単体には併合する隣接辺がある。
方針：併合がなければ全頂点が一点となり、非退化な頂点の下限と矛盾する。
規約：元のnerveの非退化性から実際の辺の存在を出す。使われ方：Riehl–Verity §4.1。 -/
lemma walkingAdjunctionExists_bottom_merge {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : Fin (n + 2) ⥤ walkingAdjunctionHom .minus Y)
    (hlast : walkingAdjunctionOrdinalCard .minus Y (H.obj (Fin.last (n + 1))) = 1)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1)) :
    ∃ k, WalkingAdjunctionBottomMergeAt H k := by
  by_contra hn
  have hno : ∀ k, ¬ WalkingAdjunctionBottomMergeAt H k := fun k hk => hn ⟨k, hk⟩
  obtain ⟨i, hi⟩ := walkingAdjunctionHomShape_exists_large_vertex H hnd
  have hc := walkingAdjunctionCard_one_of_no_bottom_merge H hlast hno i
  omega

/-- 概要：併合の位置の始頂点には少なくとも二点ある。
方針：実証人の値1とその有限上限を使う。規約：選択の仮定は足さない。
使われ方：Riehl–Verity §4.1の実併合の対象の構成。 -/
lemma WalkingAdjunctionBottomMergeAt.card_two_le {n : ℕ} {Y : WalkingAdjunctionPoint}
    {H : Fin (n + 2) ⥤ walkingAdjunctionHom .minus Y} {k : Fin (n + 1)}
    (h : WalkingAdjunctionBottomMergeAt H k) :
    2 ≤ walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc) := by
  rcases h with ⟨i, hi, _⟩
  have hp := i.isLt
  omega

/-- 概要：併合の位置では値1の全ての点の像が0。
方針：有限点は値で一意なので実証人に戻す。規約：元の実射の表示を使う。
使われ方：Riehl–Verity §4.1の実残余射の構成。 -/
lemma WalkingAdjunctionBottomMergeAt.one_zero {n : ℕ} {Y : WalkingAdjunctionPoint}
    {H : Fin (n + 2) ⥤ walkingAdjunctionHom .minus Y} {k : Fin (n + 1)}
    (h : WalkingAdjunctionBottomMergeAt H k) :
    ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)), i.val = 1 →
      (walkingAdjunctionOrderHom (H.map (homOfLE (Fin.castSucc_le_succ k))) i).val = 0 := by
  rcases h with ⟨j, hj, hz⟩
  intro i hi
  have he : i = j := Fin.ext (hi.trans hj.symm)
  exact he ▸ hz

end SerrePositivity.InfinityCategories.HA.Monads
