module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.SubdivisionIntervals

/-!
# 通常の退化の特別な頂点の逆像

概要：二つの隣接する退化の指定頂点の逆像を有限数値の式で記述する。
方針：predAbove の値を、添字以下ではそのまま、先では一つ引く式にする。
規約：Moss 2020 Lemma 26 (7) の singleton 上の計算の補助。
使われ方：二重の拡張退化を通常の退化へ比較する。

対応節は Kerodon 3.3（Tag 00XF）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open CategoryTheory

/--
概要：退化写像の頂点の値を自然数の式で表す。
方針：predAbove の定義で添字との比較を場合分けする。
規約：通常の σ^k の添字以下は不変、それより先は一つ下げる。
使われ方：Moss Lemma 26 (7) の指定頂点の逆像。
-/
theorem liftedDegeneracy_val (n : ℕ) (k : Fin (n + 1)) (i : ULift.{u} (Fin (n + 2))) :
    (liftedDegeneracy n k i).down.val =
      if i.down.val ≤ k.val then i.down.val else i.down.val - 1 := by
  change (k.predAbove i.down).val = _
  by_cases h : i.down ≤ k.castSucc
  · rw [Fin.predAbove_of_le_castSucc _ _ h]
    simp only [Fin.coe_castPred]
    rw [ite_eq_left (show i.down.val ≤ k.val from h)]
  · rw [Fin.predAbove_of_castSucc_lt _ _ (lt_of_not_ge h)]
    simp only [Fin.val_pred]
    rw [ite_eq_right (show ¬ i.down.val ≤ k.val from h)]

/--
概要：退化で k+1 に送られる頂点は k+2 だけである。
方針：退化の自然数の式を解く。
規約：Moss 2020 Lemma 26 (7) の最初の退化の逆像。
使われ方：二重拡張退化の特別な場合を区別する。
-/
theorem liftedDegeneracy_next_fiber (n : ℕ) (k : Fin (n + 1))
    (i : ULift.{u} (Fin (n + 3))) :
    liftedDegeneracy (n + 1) k.castSucc i = ULift.up k.succ ↔ i = ULift.up k.succ.succ := by
  constructor
  · intro h
    have hv := congrArg (fun j : ULift.{u} (Fin (n + 2)) => j.down.val) h
    rw [liftedDegeneracy_val] at hv
    apply ULift.ext
    apply Fin.ext
    simp only [Fin.val_castSucc, Fin.val_succ] at hv ⊢
    split_ifs at hv <;> omega
  · intro h
    subst i
    apply ULift.ext
    apply Fin.ext
    rw [liftedDegeneracy_val]
    simp only [Fin.val_castSucc, Fin.val_succ]
    split_ifs <;> omega

/--
概要：退化で重なる添字 k+1 の逆像は隣接する二つの頂点である。
方針：退化の自然数の式の二つの場合を解く。
規約：Moss 2020 Lemma 26 (7) の二番目の退化の逆像。
使われ方：通常の退化の後に特別な頂点へ入る場合。
-/
theorem liftedDegeneracy_self_fiber (n : ℕ) (k : Fin (n + 1))
    (i : ULift.{u} (Fin (n + 3))) :
    liftedDegeneracy (n + 1) k.succ i = ULift.up k.succ ↔
      i = ULift.up k.castSucc.succ ∨ i = ULift.up k.succ.succ := by
  constructor
  · intro h
    have hv := congrArg (fun j : ULift.{u} (Fin (n + 2)) => j.down.val) h
    rw [liftedDegeneracy_val] at hv
    simp only [Fin.val_succ] at hv
    split_ifs at hv with hval
    · left
      apply ULift.ext
      apply Fin.ext
      exact hv
    · right
      apply ULift.ext
      apply Fin.ext
      simp only [Fin.val_succ]
      omega
  · rintro (h | h) <;> subst i <;> apply ULift.ext <;> apply Fin.ext <;>
      rw [liftedDegeneracy_val] <;> dsimp only [Fin.val_castSucc, Fin.val_succ] <;>
      split_ifs <;> omega

/--
概要：通常の退化は指定添字自身の castSucc をその添字に送る。
方針：predAbove の同じ添字の式を使う。
規約：Moss 2020 Lemma 26 (7) の隣接頂点の計算。
使われ方：拡張退化で加える初期区間の像。
-/
theorem liftedDegeneracy_castSucc (n : ℕ) (k : Fin (n + 1)) :
    liftedDegeneracy.{u} n k (ULift.up k.castSucc) = ULift.up k := by
  apply ULift.ext
  exact Fin.predAbove_castSucc_self k

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
