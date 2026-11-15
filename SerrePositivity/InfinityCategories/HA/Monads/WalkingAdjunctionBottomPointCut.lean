module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionZeroReflection
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionCutFactorization

/-!
概要：実併合がないminus始点の全鎖から、最初の一点の実水平因子を切り出す。
方針：全実射の0の反映で座標1の切れ目を作り、既存の実区間分解を適用する。
規約：実分解の存在や全射の自然性を入力に追加しない。
使われ方：Riehl–Verity Lemma 4.1.4の実親の逆方向、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の始点plusの実因子の回収。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：併合のない実全鎖の最初の一点の右にあるplusの実切れ目。
方針：全点の値0と0の逆像の反映で区間表示の切れ目の自然性を示す。
規約：全実射の可換性を構成。使われ方：Riehl–Verity Lemma 4.1.4の実水平分解。 -/
def walkingAdjunctionBottomPointCut {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) n)
    (hno : ∀ k : Fin n, ∀ a : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      a.val = 1 → (walkingAdjunctionOrderHom
        (H.map (homOfLE (Fin.castSucc_le_succ k))) a).val ≠ 0) : WalkingAdjunctionPlusCut H where
  value i := ⟨1, by
    have hp := NeZero.pos (walkingAdjunctionOrdinalCard .minus Y (H.obj i))
    omega⟩
  naturality {i j} hij := by
    apply ordinalIntervalMap_cut_unique
    intro a
    constructor
    · intro ha
      have hz : a.val = 0 := by change a.val < 1 at ha; omega
      have hf := walkingAdjunctionOrderHom_bottom (H.map (homOfLE hij)) a hz
      change (walkingAdjunctionOrderHom (H.map (homOfLE hij)) a).val < 1
      omega
    · intro ha
      have hz : (walkingAdjunctionOrderHom (H.map (homOfLE hij)) a).val = 0 := by
        change (walkingAdjunctionOrderHom (H.map (homOfLE hij)) a).val < 1 at ha
        omega
      have he := walkingAdjunctionReflectsZeroMap_of_no_bottom_merge H hno hij a hz
      change a.val < 1
      omega

/-- 概要：最初の一点の切れ目の全実座標は1。
方針：構成した実切れ目の定義を評価する。規約：全頂点。
使われ方：Riehl–Verity Lemma 4.1.4の前置生成射の回収。 -/
lemma walkingAdjunctionBottomPointCut_val {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) n)
    (hno : ∀ k : Fin n, ∀ a : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      a.val = 1 → (walkingAdjunctionOrderHom
        (H.map (homOfLE (Fin.castSucc_le_succ k))) a).val ≠ 0) (i : Fin (n + 1)) :
    ((walkingAdjunctionBottomPointCut H hno).value i).val = 1 := by
  rfl

/-- 概要：終点が二点で併合のない実全鎖を、最初の一点と残りへ実水平分解する。
方針：実切れ目が両外端の間にあることを個数から検収し、全区間の実分解を適用する。
規約：左右の実関手と全合成の等式を構成。使われ方：Riehl–Verity Lemma 4.1.4の逆方向。 -/
def walkingAdjunctionBottomPointFactorization {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) n)
    (hno : ∀ k : Fin n, ∀ a : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      a.val = 1 → (walkingAdjunctionOrderHom
        (H.map (homOfLE (Fin.castSucc_le_succ k))) a).val ≠ 0)
    (hlast : walkingAdjunctionOrdinalCard .minus Y (H.obj (Fin.last n)) = 2) :
    WalkingAdjunctionFactorization H :=
  let a := walkingAdjunctionBottomPointCut H hno
  walkingAdjunctionFactorizationOfCut (M := .plus) a
    (a.source_le (by intro _; exact Nat.zero_lt_one))
    (a.le_target (by
      intro _
      change 1 < walkingAdjunctionOrdinalCard .minus Y (H.obj (Fin.last n))
      omega))

/-- 概要：切り出した左の実因子は全頂点で一点を持つ。
方針：区間の個数を座標1と元の左外端0から計算する。
規約：実分解の左因子。使われ方：Riehl–Verity Lemma 4.1.4の実生成射との照合。 -/
lemma walkingAdjunctionBottomPointFactorization_left_card {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) n)
    (hno : ∀ k : Fin n, ∀ a : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      a.val = 1 → (walkingAdjunctionOrderHom
        (H.map (homOfLE (Fin.castSucc_le_succ k))) a).val ≠ 0)
    (hlast : walkingAdjunctionOrdinalCard .minus Y (H.obj (Fin.last n)) = 2)
    (i : Fin (n + 1)) :
    walkingAdjunctionOrdinalCard .minus .plus
      ((walkingAdjunctionBottomPointFactorization H hno hlast).left.obj i) = 1 := by
  change walkingAdjunctionOrdinalCard .minus .plus
    (walkingAdjunctionCutIntervalObject (walkingAdjunctionSourceCut H)
      (M := .minus) (N := .plus) (walkingAdjunctionBottomPointCut H hno)
      ((walkingAdjunctionBottomPointCut H hno).source_le (by
        intro _
        exact Nat.zero_lt_one)) i) = 1
  rw [walkingAdjunctionCutIntervalObject_card]
  change 1 - walkingAdjunctionCutCoordinate (walkingAdjunctionSourceCut H) i + 0 = 1
  rw [walkingAdjunctionSourceCut_coordinate]

end SerrePositivity.InfinityCategories.HA.Monads
