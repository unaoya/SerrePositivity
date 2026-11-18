module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Renaming
public import Mathlib.Data.Finset.Max

/-!
模型。文献の定義との比較は後で
# 全射語の最後の出現と表の区切り

概要：Berger–Fresse §1.2.2 の caesura は、語で最後の出現ではない位置である。
方針：各値の出現集合の最大を取り、最終出現位置の集合を値集合と同定する。
規約：順序は語の位置の順序であり、値の大小には依存しない。
使われ方：表の行数と削除微分の交代符号を定める。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：同じ値が後にも現れる位置は表の区切り（BF §1.2.2）。
方針：より後の同じ値の存在で定める。
規約：最後の行の末尾は区切りに含めない。
使われ方：表の行と削除微分の交代符号を構成する。 -/
def Caesura {n l : ℕ} (u : Fin l → Fin n) (i : Fin l) : Prop :=
  ∃ j : Fin l, i < j ∧ u j = u i

/-- 概要：区切り位置は有限計算で判定できる（BF §1.2.2）。
方針：後の全ての文字を調べる。
規約：全射性や非退化性は不要。
使われ方：符号の指数を有限和で計算する。 -/
instance _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.instDecidableCaesura {n l : ℕ} (u : Fin l → Fin n) (i : Fin l) : Decidable (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u i) := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura
  infer_instance

/-- 概要：値の置換は区切り位置を保つ（BF §1.2.2）。
方針：同じ値の出現を置換の単射性で比較する。
規約：位置は動かさない。
使われ方：削除微分の符号の同変性を証明する。 -/
lemma caesura_rename_iff {n l : ℕ} (σ : Equiv.Perm (Fin n))
    (u : Fin l → Fin n) (i : Fin l) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura (σ ∘ u) i ↔ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u i := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura, Function.comp_apply, Equiv.apply_eq_iff_eq]

/-- 概要：指定した値の全出現位置の集合（BF §1.2.2）。
方針：有限な位置集合から値が一致するものを取る。
規約：空の出現集合も扱う。
使われ方：最終出現と直前の出現を選ぶ。 -/
def occurrences {n l : ℕ} (u : Fin l → Fin n) (k : Fin n) : Finset (Fin l) :=
  Finset.univ.filter (fun i => u i = k)

namespace Word

variable {n l : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word n l)

/-- 概要：全射語では各値の出現集合は非空（BF §1.2.2）。
方針：全射性から得た出現を集合へ入れる。
規約：各値について主張するので arity 0 も扱える。
使われ方：最後の出現の最大値を定義する。 -/
lemma occurrences_nonempty (k : Fin n) : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences u.val k).Nonempty := by
  obtain ⟨i, hi⟩ := u.surjective k
  exact ⟨i, by simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences, hi]⟩

/-- 概要：全射語の各値の最後の出現位置（BF §1.2.2）。
方針：非空な出現集合の最大を取る。
規約：値を比較する順序を使わない。
使われ方：表の区切りでない位置を値集合と同定する。 -/
def lastOccurrence (k : Fin n) : Fin l :=
  (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences u.val k).max' (u.occurrences_nonempty k)

/-- 概要：最後の出現の文字は指定した値（BF §1.2.2）。
方針：最大値が出現集合に属することを使う。
規約：語の位置での等式。
使われ方：最終出現位置の全射性を得る。 -/
@[simp]
lemma lastOccurrence_value (k : Fin n) : u.val (u.lastOccurrence k) = k := by
  have h := Finset.max'_mem (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences u.val k) (u.occurrences_nonempty k)
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word.lastOccurrence, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences, Finset.mem_filter, Finset.mem_univ, true_and] using h

/-- 概要：各値の最後の出現は表の区切りではない（BF §1.2.2）。
方針：より後の出現があれば出現集合の最大性に矛盾する。
規約：同じ値の出現回数に制限はない。
使われ方：最終出現位置の同値を構成する。 -/
lemma not_caesura_lastOccurrence (k : Fin n) : ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u.val (u.lastOccurrence k) := by
  rintro ⟨j, hj, heq⟩
  have hjk : j ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences u.val k := by simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences, heq]
  exact (not_lt_of_ge (Finset.le_max' _ j hjk)) hj

/-- 概要：最終出現位置の集合は値集合と同値（BF §1.2.2）。
方針：語の評価を使い、逆方向には最後の出現を取る。
規約：位置の部分型を値で同定する。
使われ方：区切りの個数が次数に等しいことを示す。 -/
noncomputable def finalPositionEquiv : {i : Fin l // ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u.val i} ≃ Fin n :=
  Equiv.ofBijective (fun i => u.val i.val) ⟨by
    intro i j hij
    apply Subtype.ext
    rcases lt_trichotomy i.val j.val with h | h | h
    · exact False.elim (i.property ⟨j.val, h, hij.symm⟩)
    · exact h
    · exact False.elim (j.property ⟨i.val, h, hij⟩), by
    intro k
    exact ⟨⟨u.lastOccurrence k, u.not_caesura_lastOccurrence k⟩,
      u.lastOccurrence_value k⟩⟩

/-- 概要：最終出現位置は arity と同じ個数だけある（BF §1.2.2）。
方針：最終出現位置と値集合の同値の濃度を比較する。
規約：arity 0 も含む。
使われ方：区切りの濃度を計算する。 -/
lemma card_final_positions : Fintype.card {i : Fin l // ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u.val i} = n := by
  simpa only [Fintype.card_fin] using Fintype.card_congr u.finalPositionEquiv

/-- 概要：区切りの個数は語の長さから arity を引いたもの（BF §1.2.2）。
方針：全位置から最終出現位置を除いた濃度を計算する。
規約：全射語なので長さは arity 以上。
使われ方：次数 d の表の区切りが d 個であることを得る。 -/
lemma card_caesuras : Fintype.card {i : Fin l // _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u.val i} = l - n := by
  have h := Fintype.card_subtype_compl (fun i : Fin l => ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u.val i)
  simpa only [not_not, Fintype.card_fin, u.card_final_positions] using h

end Word

/-- 概要：次数 d の基底語の区切りはちょうど d 個（BF §1.2.2）。
方針：長さ n+d での区切りの個数を簡約する。
規約：空語では区切りは零個。
使われ方：表の d+1 行と交代符号の指数を確定する。 -/
lemma card_caesuras_basisWord {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) :
    Fintype.card {i : Fin (n + d) // _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u.val i} = d := by
  simpa only [Nat.add_sub_cancel_left] using u.card_caesuras

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
