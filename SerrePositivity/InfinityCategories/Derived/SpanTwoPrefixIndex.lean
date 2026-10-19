module
public import SerrePositivity.InfinityCategories.Derived.SpanOnePrefixIndex

/-! # 固定二点を含む未知集合の切断と符号

概要：標準セル全体の余錐頂点と二番目の固定点での切断・削除・符号を計算する。
方針：先頭の値零・一と、二以上の終区間による頂点の分類を使う。
規約：HA Proposition 1.3.1.10。使われ方：D7 の三角形成分の二つの残差寄与。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.InfinityCategories
open DGNerve

/-- 概要：後続集合に固定二点を加えると全体集合になる。
方針：全頂点の三分類を使う。
規約：全次元。使われ方：第四の未知集合の表示。 -/
lemma spanSuffix_insert_both (n : ℕ) :
    insert (spanFirstPrefix n) (insert (spanSecondPrefix n) (spanSuffixFaces n)) =
      Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro i
  rcases spanVertex_cases i with hi | rfl | rfl
  · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hi)
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)

/-- 概要：二番目の固定点は最初の点より大きい。
方針：値零と一を比較する。
規約：固定点の番号。使われ方：Bianchi の内部点。 -/
lemma spanSecondPrefix_pos (n : ℕ) : (0 : Fin (n + 4)) < spanSecondPrefix n := by
  change (0 : ℕ) < 1
  norm_num [spanApex, spanSecondPrefix]

/-- 概要：二番目の固定点は余錐頂点より前にある。
方針：値一と二を比較する。
規約：固定点と可変点の境界。使われ方：二寄与の分離。 -/
lemma spanSecondPrefix_lt_apex (n : ℕ) : spanSecondPrefix n < spanApex n := by
  change (1 : ℕ) < 2
  norm_num [spanApex, spanSecondPrefix]

/-- 概要：余錐頂点は最初の点より大きい。
方針：二番目の固定点を経由する。
規約：全次元。使われ方：Bianchi の内部点。 -/
lemma spanApex_pos (n : ℕ) : (0 : Fin (n + 4)) < spanApex n :=
  (spanSecondPrefix_pos n).trans (spanSecondPrefix_lt_apex n)

/-- 概要：全体集合の余錐頂点以上の右切断は後続集合。
方針：終区間による所属条件を使う。
規約：全次元。使われ方：後続残差の出現位置。 -/
lemma spanUniv_rightCut_apex (n : ℕ) :
    (Finset.univ : Finset (Fin (n + 4))).filter (spanApex n ≤ ·) = spanSuffixFaces n := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_spanSuffixFaces_iff_le]

/-- 概要：全体集合の余錐頂点以下の左切断は先頭三点。
方針：二以下の自然数の値を分類する。
規約：先頭三点は元の余錐の三角形。使われ方：ホモトピー成分との合成。 -/
lemma spanUniv_leftCut_apex (n : ℕ) :
    (Finset.univ : Finset (Fin (n + 4))).filter (· ≤ spanApex n) =
      {0, spanSecondPrefix n, spanApex n} := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
  change i.val ≤ 2 ↔ i = 0 ∨ i = spanSecondPrefix n ∨ i = spanApex n
  constructor
  · intro hi
    by_cases h0 : i.val = 0
    · exact Or.inl (Fin.ext h0)
    by_cases h1 : i.val = 1
    · exact Or.inr (Or.inl (Fin.ext h1))
    · exact Or.inr (Or.inr (Fin.ext (by change i.val = 2; omega)))
  · rintro (rfl | rfl | rfl) <;> norm_num [spanApex, spanSecondPrefix]

/-- 概要：二番目の固定点以下の左切断は固定二点。
方針：一以下の値を分類する。
規約：元の span の脚。使われ方：脚との残差合成。 -/
lemma spanUniv_leftCut_secondPrefix (n : ℕ) :
    (Finset.univ : Finset (Fin (n + 4))).filter (· ≤ spanSecondPrefix n) =
      {0, spanSecondPrefix n} := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
  change i.val ≤ 1 ↔ i = 0 ∨ i = spanSecondPrefix n
  constructor
  · intro hi
    by_cases h0 : i.val = 0
    · exact Or.inl (Fin.ext h0)
    · exact Or.inr (Fin.ext (by change i.val = 1; omega))
  · rintro (rfl | rfl) <;> norm_num [spanApex, spanSecondPrefix]

/-- 概要：二番目の固定点以上の右切断はその点と後続集合。
方針：一以上の値は一自身または二以上である。
規約：全次元。使われ方：脚側の残差の特定。 -/
lemma spanUniv_rightCut_secondPrefix (n : ℕ) :
    (Finset.univ : Finset (Fin (n + 4))).filter (spanSecondPrefix n ≤ ·) =
      insert (spanSecondPrefix n) (spanSuffixFaces n) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    mem_spanSuffixFaces]
  change 1 ≤ i.val ↔ i = spanSecondPrefix n ∨ 2 ≤ i.val
  constructor
  · intro hi
    by_cases h1 : i.val = 1
    · exact Or.inl (Fin.ext h1)
    · exact Or.inr (by omega)
  · rintro (rfl | hi)
    · norm_num [spanApex, spanSecondPrefix]
    · omega

/-- 概要：二番目の固定点を消すと最初の固定点と後続集合が残る。
方針：値一でない点を零または二以上に分類する。
規約：全体集合の削除。使われ方：共通の A 側残差の特定。 -/
lemma spanUniv_erase_secondPrefix (n : ℕ) :
    (Finset.univ : Finset (Fin (n + 4))).erase (spanSecondPrefix n) =
      insert (0 : Fin (n + 4)) (spanSuffixFaces n) := by
  ext i
  simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_insert, mem_spanSuffixFaces]
  have hv : i ≠ spanSecondPrefix n ↔ i.val ≠ 1 := by
    constructor
    · intro h he
      exact h (Fin.ext he)
    · intro h he
      exact h (congrArg Fin.val he)
  rw [hv]
  constructor
  · intro hi
    by_cases h0 : i.val = 0
    · exact Or.inl (Fin.ext h0)
    · exact Or.inr (by omega)
  · rintro (rfl | hi)
    · norm_num [spanApex, spanSecondPrefix]
    · omega

/-- 概要：余錐頂点より後の点は後続集合からその頂点を消した集合。
方針：全体集合と一点追加集合の同じ狭義終区間を比較する。
規約：固定点は数えない。使われ方：余錐頂点の符号の指数。 -/
lemma spanUniv_above_apex (n : ℕ) :
    (Finset.univ : Finset (Fin (n + 4))).filter (spanApex n < ·) =
      (spanSuffixFaces n).erase (spanApex n) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
    mem_spanSuffixFaces_iff_le]
  exact lt_iff_le_and_ne.trans (by tauto)

/-- 概要：二番目の固定点より後の点は後続集合。
方針：一より大きい値と二以上の値を比較する。
規約：全次元。使われ方：固定点側の寄与の符号。 -/
lemma spanUniv_above_secondPrefix (n : ℕ) :
    (Finset.univ : Finset (Fin (n + 4))).filter (spanSecondPrefix n < ·) = spanSuffixFaces n := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_spanSuffixFaces]
  change 1 < i.val ↔ 2 ≤ i.val
  omega

/-- 概要：余錐頂点の寄与の符号は (-1)^(n+1)。
方針：後続の n+2 点から余錐頂点を除いた点を数える。
規約：整数の単位群の符号。使われ方：ホモトピー成分との合成項。 -/
lemma spanUniv_sign_apex (n : ℕ) :
    Index.sign (Finset.univ : Finset (Fin (n + 4))) (spanApex n) =
      ((n : ℤ) + 1).negOnePow := by
  have hc := Finset.card_erase_add_one
    ((mem_spanSuffixFaces_iff_le (spanApex n)).mpr le_rfl)
  rw [card_spanSuffixFaces] at hc
  have he : ((spanSuffixFaces n).erase (spanApex n)).card = n + 1 := by omega
  simp only [Index.sign, spanUniv_above_apex, he, Nat.cast_add, Nat.cast_one]

/-- 概要：二番目の固定点の寄与の符号は (-1)^(n+2)。
方針：後続の n+2 点を全て数える。
規約：整数の単位群の符号。使われ方：削除項と脚側の残差項。 -/
lemma spanUniv_sign_secondPrefix (n : ℕ) :
    Index.sign (Finset.univ : Finset (Fin (n + 4))) (spanSecondPrefix n) =
      ((n : ℤ) + 2).negOnePow := by
  simp only [Index.sign, spanUniv_above_secondPrefix, card_spanSuffixFaces,
    Nat.cast_add, Nat.cast_ofNat]

end SerrePositivity.InfinityCategories
