module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionBottomMergePositions

/-!
概要：隣接する全実辺で底の二点の併合がなければ、全実射が0の逆像を反映する。
方針：終点への実射を逆帰納し、一般の射を終点への合成に入れる。
規約：長さ0を含み、元の実関手の全合成を保持する。
使われ方：Riehl–Verity Lemma 4.1.4の実親の逆方向、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の一点の実因子の回収。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：全隣接実辺で併合がなければ、終点への全実射が0の逆像を反映する。
方針：終点の恒等射を基底として一辺ずつ逆帰納する。
規約：長さ0でも同じ結論。使われ方：Riehl–Verity Lemma 4.1.4の実因子の回収。 -/
lemma walkingAdjunctionReflectsZeroToLast_of_no_bottom_merge {n : ℕ}
    {Y : WalkingAdjunctionPoint} (H : ComposableArrows (walkingAdjunctionHom .minus Y) n)
    (hno : ∀ k : Fin n, ∀ a : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      a.val = 1 → (walkingAdjunctionOrderHom
        (H.map (homOfLE (Fin.castSucc_le_succ k))) a).val ≠ 0) :
    ∀ (i : Fin (n + 1)) (a : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj i))),
      (walkingAdjunctionOrderHom (H.map (homOfLE (Fin.le_last i))) a).val = 0 → a.val = 0 := by
  intro i
  induction i using Fin.reverseInduction with
  | last =>
    intro a ha
    have he : homOfLE (Fin.le_last (Fin.last n)) = 𝟙 (Fin.last n) := Subsingleton.elim _ _
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
    exact ordinalReflectsZero_of_no_one (walkingAdjunctionOrderHom f) (hno k) a (ih b hz)

/-- 概要：全隣接実辺で併合がなければ、全実射が0の逆像を反映する。
方針：終点まで合成し、後半の実射の最小元保存と終点への反映を合わせる。
規約：全頂点間の元の射。使われ方：Riehl–Verity Lemma 4.1.4の一点の実切れ目。 -/
lemma walkingAdjunctionReflectsZeroMap_of_no_bottom_merge {n : ℕ}
    {Y : WalkingAdjunctionPoint} (H : ComposableArrows (walkingAdjunctionHom .minus Y) n)
    (hno : ∀ k : Fin n, ∀ a : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      a.val = 1 → (walkingAdjunctionOrderHom
        (H.map (homOfLE (Fin.castSucc_le_succ k))) a).val ≠ 0)
    {i j : Fin (n + 1)} (hij : i ≤ j)
    (a : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj i)))
    (ha : (walkingAdjunctionOrderHom (H.map (homOfLE hij)) a).val = 0) : a.val = 0 := by
  apply walkingAdjunctionReflectsZeroToLast_of_no_bottom_merge H hno i a
  have he : H.map (homOfLE (Fin.le_last i)) =
      H.map (homOfLE hij) ≫ H.map (homOfLE (Fin.le_last j)) := by
    rw [← H.map_comp]
    rfl
  rw [he, walkingAdjunctionOrderHom_comp]
  exact walkingAdjunctionOrderHom_bottom (H.map (homOfLE (Fin.le_last j))) _ ha

end SerrePositivity.InfinityCategories.HA.Monads
