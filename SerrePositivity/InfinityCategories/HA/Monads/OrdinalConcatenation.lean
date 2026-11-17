module

public import SerrePositivity.InfinityCategories.HA.Monads.OrdinalIntervalHom
public import SerrePositivity.InfinityCategories.HA.Monads.OrdinalSumFunctor

/-!
概要：水平合成の有限順序射を、順序和と端点共有の貼り合わせの値で比較する。
方針：Finの和の分割と自然数の値による場合分けを使う。
規約：順序和の因子は空も許し、貼り合わせの二因子は非空。
使われ方：HA Proposition 4.7.3.3、Riehl–Verity Remark 3.3.8 の残る混合水平結合則。
Kerodon Remark 6.2.1.4（Tag 02EN）。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.HA.Monads

variable {m n p q r s : ℕ}

/-- 概要：空も許す有限単調射の順序和。
方針：Fin.addCasesで二つの区間を貼る。規約：点の個数で添字付ける。
使われ方：Riehl–Verity Remark 3.3.8 の既存の順序和の射の計算。 -/
def ordinalAppend (f : Fin m →o Fin n) (g : Fin p →o Fin q) :
    Fin (m + p) →o Fin (n + q) where
  toFun := Fin.addCases (fun i => (f i).castAdd q) (fun j => (g j).natAdd n)
  monotone' := by
    intro i j h
    cases i using Fin.addCases <;> cases j using Fin.addCases <;>
      rw [Fin.le_def] at h ⊢ <;> simp at h ⊢ <;> grind only [OrderHom.apply_mono]

/-- 概要：順序和の左の点での値。
方針：Fin.addCasesの定義。規約：元の点の等式。
使われ方：Riehl–Verity Remark 3.3.8 の水平合成の射の比較。 -/
@[simp] lemma ordinalAppend_castAdd (f : Fin m →o Fin n) (g : Fin p →o Fin q) (i : Fin m) :
    ordinalAppend f g (i.castAdd p) = (f i).castAdd q := by
  simp [ordinalAppend]

/-- 概要：順序和の右の点での値。
方針：Fin.addCasesの右の枝。規約：左の個数だけずらす。
使われ方：Riehl–Verity Remark 3.3.8 の水平合成の射の比較。 -/
@[simp] lemma ordinalAppend_natAdd (f : Fin m →o Fin n) (g : Fin p →o Fin q) (i : Fin p) :
    ordinalAppend f g (i.natAdd m) = (g i).natAdd n := by
  simp [ordinalAppend]

/-- 概要：左の区間内にある任意の点での順序和の値。
方針：左の包含の像として点を表示する。規約：値の自然数で比較する。
使われ方：Riehl–Verity Remark 3.3.8 の結合則の有限順序計算。 -/
lemma ordinalAppend_val_left (f : Fin m →o Fin n) (g : Fin p →o Fin q)
    (i : Fin (m + p)) (hi : i.val < m) :
    (ordinalAppend f g i).val = (f ⟨i.val, hi⟩).val := by
  have h : i = (⟨i.val, hi⟩ : Fin m).castAdd p := rfl
  conv_lhs => rw [h, ordinalAppend_castAdd]
  rfl

/-- 概要：右の区間内にある任意の点での順序和の値。
方針：左の個数を引いて右の包含の像にする。規約：空も含む。
使われ方：Riehl–Verity Remark 3.3.8 の結合則の有限順序計算。 -/
lemma ordinalAppend_val_right (f : Fin m →o Fin n) (g : Fin p →o Fin q)
    (i : Fin (m + p)) (hi : m ≤ i.val) :
    (ordinalAppend f g i).val = n + (g ⟨i.val - m, by have := i.isLt; omega⟩).val := by
  have h : i = (⟨i.val - m, by have := i.isLt; omega⟩ : Fin p).natAdd m := by
    apply Fin.ext
    dsimp
    omega
  conv_lhs => rw [h, ordinalAppend_natAdd]
  rfl

/-- 概要：有限区間の射を一つの端点を共有して貼り合わせる。
方針：共有点までは左の射、共有点の後は右の射をずらす。
規約：写像自体は任意。関手の合成則に使うときは左の最大元・右の最小元の条件を別に照合する。
使われ方：Riehl–Verity Remark 3.3.8 の混合水平合成の射の表示。 -/
def ordinalGlue (f : Fin (m + 1) →o Fin (n + 1))
    (g : Fin (p + 1) →o Fin (q + 1)) : Fin (m + p + 1) →o Fin (n + q + 1) where
  toFun i := if h : i.val ≤ m then
      ⟨(f ⟨i.val, by omega⟩).val, by have := (f ⟨i.val, by omega⟩).isLt; omega⟩
    else
      ⟨n + (g ⟨i.val - m, by have := i.isLt; omega⟩).val,
        by have := (g ⟨i.val - m, by have := i.isLt; omega⟩).isLt; omega⟩
  monotone' := by
    intro i j hij
    change i.val ≤ j.val at hij
    rw [Fin.le_def]
    dsimp only
    split_ifs with hi hj
    · exact f.monotone hij
    · change (f ⟨i.val, by omega⟩).val ≤
        n + (g ⟨j.val - m, by have := j.isLt; omega⟩).val
      have := (f ⟨i.val, by omega⟩).isLt
      omega
    · omega
    · change n + (g ⟨i.val - m, by have := i.isLt; omega⟩).val ≤
        n + (g ⟨j.val - m, by have := j.isLt; omega⟩).val
      have h : (g ⟨i.val - m, by have := i.isLt; omega⟩).val ≤
          (g ⟨j.val - m, by have := j.isLt; omega⟩).val :=
        g.monotone (Nat.sub_le_sub_right hij m)
      exact Nat.add_le_add_left h n

/-- 概要：貼り合わせの左の区間の点での値。
方針：共有点を含む左の枝を計算する。規約：左の全点。
使われ方：Riehl–Verity Remark 3.3.8 の混合水平合成の射の照合。 -/
@[simp] lemma ordinalGlue_val_left (f : Fin (m + 1) →o Fin (n + 1))
    (g : Fin (p + 1) →o Fin (q + 1)) (i : Fin (m + 1)) :
    (ordinalGlue f g ⟨i.val, by have := i.isLt; omega⟩).val = (f i).val := by
  have hi : i.val ≤ m := by have := i.isLt; omega
  simp [ordinalGlue, hi]

/-- 概要：貼り合わせの右の区間の点での値。
方針：共有点は両端点保存で照合し、他の点は右の枝を使う。
規約：左の最大元と右の最小元の条件を明示する。
使われ方：Riehl–Verity Remark 3.3.8 の混合水平合成の射の照合。 -/
lemma ordinalGlue_val_right (f : Fin (m + 1) →o Fin (n + 1))
    (g : Fin (p + 1) →o Fin (q + 1)) (hf : f (Fin.last m) = Fin.last n) (hg : g 0 = 0)
    (i : Fin (p + 1)) :
    (ordinalGlue f g ⟨m + i.val, by have := i.isLt; omega⟩).val = n + (g i).val := by
  by_cases hi : i = 0
  · subst i
    simpa only [hf, hg, Fin.val_last, Fin.val_zero, Nat.add_zero] using
      ordinalGlue_val_left f g (Fin.last m)
  · have hpos : 0 < i.val := by
      have : i.val ≠ 0 := fun h => hi (Fin.ext h)
      omega
    simp [ordinalGlue, show ¬ m + i.val ≤ m by omega]

/-- 概要：異なる表示の有限単調射を値から比較する。
方針：個数の等式で戻して外延性を使う。規約：型の輸送を隠さずHEqで保持する。
使われ方：HA Proposition 4.7.3.3 の水平結合則での対象等式の輸送。 -/
lemma ordinalHom_hext {a b c d : ℕ} (hac : a = c) (hbd : b = d)
    (f : Fin a →o Fin b) (g : Fin c →o Fin d)
    (h : ∀ (i : Fin a) (j : Fin c), i.val = j.val → (f i).val = (g j).val) : HEq f g := by
  subst c
  subst d
  apply heq_of_eq
  apply OrderHom.ext
  funext i
  exact Fin.ext (h i i rfl)

end SerrePositivity.InfinityCategories.HA.Monads
