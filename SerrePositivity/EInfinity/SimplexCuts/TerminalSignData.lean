module

public import SerrePositivity.EInfinity.SimplexCuts.TerminalEndpoints

/-!
# 接頭部から復元する BF 符号の有限データ

Berger–Fresse §2.2.4・§2.2.7、M14 L09a。
元の語のcaesuraを保持したまま、復元切断のlo・hiを数値の式で評価する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 接頭部内にある元の区間番号を、接頭部の番号として読む。 -/
def prefixIndexOfLE {m : ℕ} (p i : Fin (m + 1)) (h : i ≤ p) : Fin (p.val + 1) :=
  ⟨i.val, by change i.val ≤ p.val at h; omega⟩

/-- 復元区間の左端の数値式。 -/
def restoredLo {m q : ℕ} (p : Fin (m + 1)) (s : Cut p.val q) (i : Fin (m + 1)) : ℕ :=
  if h : i ≤ p then lo s (prefixIndexOfLE p i h) else q + 1

/-- 復元区間の右端の数値式。 -/
def restoredHi {m q : ℕ} (p : Fin (m + 1)) (s : Cut p.val q) (i : Fin (m + 1)) : ℕ :=
  if h : i < p then hi s (prefixIndexOfLE p i h.le) else q + 1

/-- C14：全区間の左端の一括評価。 -/
lemma lo_terminalExtend {m q : ℕ} (p : Fin (m + 1)) (s : Cut p.val q)
    (i : Fin (m + 1)) : lo (terminalExtend m q p s) i = restoredLo p s i := by
  unfold restoredLo
  split_ifs with h
  · have he : prefixPosition p (prefixIndexOfLE p i h) = i := Fin.ext rfl
    exact (congrArg (lo (terminalExtend m q p s)) he).symm.trans
      (lo_terminalExtend_prefix p s _)
  · exact (endpoints_terminalExtend_suffix p s i (lt_of_not_ge h)).1

/-- C15：全区間の右端の一括評価。 -/
lemma hi_terminalExtend {m q : ℕ} (p : Fin (m + 1)) (s : Cut p.val q)
    (i : Fin (m + 1)) : hi (terminalExtend m q p s) i = restoredHi p s i := by
  unfold restoredHi
  split_ifs with h
  · have he : prefixPosition p (prefixIndexOfLE p i h.le) = i := Fin.ext rfl
    exact (congrArg (hi (terminalExtend m q p s)) he).symm.trans
      (hi_terminalExtend_prefix p s _ h)
  · by_cases he : i = p
    · subst i
      exact hi_terminalExtend_at p s
    · exact (endpoints_terminalExtend_suffix p s i
        (lt_of_le_of_ne (le_of_not_gt h) (Ne.symm he))).2

/-- 元の語のcaesuraを用いた復元後の区間の符号次数。 -/
def restoredLength {m q r : ℕ} (p : Fin (m + 1)) (s : Cut p.val q)
    (v : Fin (m + 1) → Fin r) (i : Fin (m + 1)) : ℕ :=
  restoredHi p s i - restoredLo p s i + if Surjection.Caesura v i then 1 else 0

/-- C16：区間の符号次数は、復元した両端と元の語だけで計算できる。 -/
lemma intervalLength_terminalExtend {m q r : ℕ} (p : Fin (m + 1)) (s : Cut p.val q)
    (v : Fin (m + 1) → Fin r) (i : Fin (m + 1)) :
    intervalLength (terminalExtend m q p s) v i = restoredLength p s v i := by
  unfold intervalLength restoredLength
  rw [hi_terminalExtend, lo_terminalExtend]

/-- 復元した有限データで計算するBF符号の指数。 -/
def restoredSignExponent {m q r : ℕ} (p : Fin (m + 1)) (s : Cut p.val q)
    (v : Fin (m + 1) → Fin r) : ℕ :=
  (∑ i, ∑ j, if i < j ∧ v j < v i then
    restoredLength p s v i * restoredLength p s v j else 0) +
  ∑ i, if Surjection.Caesura v i then restoredHi p s i else 0

/-- C17：元の語のcaesuraを保持した、最後の垂直辺でのBF符号の再帰式。 -/
lemma cutSign_terminalExtend {m q r : ℕ} (p : Fin (m + 1)) (s : Cut p.val q)
    (v : Fin (m + 1) → Fin r) :
    cutSign (terminalExtend m q p s) v = (-1 : ℤ) ^ restoredSignExponent p s v := by
  unfold cutSign permutationExponent positionExponent restoredSignExponent
  simp_rw [intervalLength_terminalExtend, hi_terminalExtend]

end SerrePositivity.EInfinity.SimplexCuts
