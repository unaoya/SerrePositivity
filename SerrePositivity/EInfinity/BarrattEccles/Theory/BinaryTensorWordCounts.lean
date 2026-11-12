module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.BinaryTensorColorClassification

/-!
# 二色の語の濃度と標準代表

HA 3.2.4.7 の色付き Schur 分解の添字を固定する。
色の二つのファイバーの濃度の和は全 arity であり、
任意の語はその濃度の標準パターンの置換となる。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity

/-- 語の指定した色の入力数。 -/
def binaryTensorWordCount (r : ℕ) (w : BinaryTensorWord r) (b : Bool) : ℕ :=
  Fintype.card {i : Fin r // binaryTensorWordColors r w i = b}

/-- 二つの色の入力数の和は全 arity。 -/
lemma binaryTensorWordCount_sum (r : ℕ) (w : BinaryTensorWord r) :
    binaryTensorWordCount r w false + binaryTensorWordCount r w true = r := by
  classical
  have e : {i : Fin r // binaryTensorWordColors r w i ≠ false} ≃
      {i : Fin r // binaryTensorWordColors r w i = true} :=
    Equiv.subtypeEquivRight (fun i => by cases binaryTensorWordColors r w i <;> simp)
  have h := Fintype.card_congr (Equiv.sumCompl (fun i : Fin r =>
    binaryTensorWordColors r w i = false))
  simpa only [Fintype.card_sum, Fintype.card_fin, Fintype.card_congr e,
    binaryTensorWordCount] using h

/-- 置換は各色の入力数を保つ。 -/
lemma binaryTensorWordCount_smul (r : ℕ) (σ : Equiv.Perm (Fin r))
    (w : BinaryTensorWord r) (b : Bool) :
    binaryTensorWordCount r (σ • w) b = binaryTensorWordCount r w b := by
  apply Fintype.card_congr
  exact σ.symm.subtypeEquiv (fun i => by rw [binaryTensorWordColors_smul])

/-- arity の等式に沿って語の添字を移しても、色の入力数は変わらない。 -/
lemma binaryTensorWordCount_cast {r s : ℕ} (h : r = s) (w : BinaryTensorWord r) (b : Bool) :
    binaryTensorWordCount s (cast (congrArg BinaryTensorWord h) w) b =
      binaryTensorWordCount r w b := by
  subst s
  rfl

/-- 任意の語は、その二色の濃度を持つ標準パターンの置換に一致する。 -/
lemma binaryTensorWord_standard_orbit (r : ℕ) (w : BinaryTensorWord r) :
    ∃ (m n : ℕ) (h : m + n = r) (σ : Equiv.Perm (Fin r)),
      m = binaryTensorWordCount r w false ∧ n = binaryTensorWordCount r w true ∧
      σ • cast (congrArg BinaryTensorWord h) (binaryTensorStandardPattern m n) = w := by
  let m := binaryTensorWordCount r w false
  let n := binaryTensorWordCount r w true
  have h : m + n = r := binaryTensorWordCount_sum r w
  refine ⟨m, n, h, ?_⟩
  have hc (b : Bool) :
      binaryTensorWordCount r
        (cast (congrArg BinaryTensorWord h) (binaryTensorStandardPattern m n)) b =
          binaryTensorWordCount r w b := by
    rw [binaryTensorWordCount_cast h (binaryTensorStandardPattern m n) b]
    change Fintype.card _ = _
    rw [binaryTensorStandardPattern_card]
    cases b <;> rfl
  obtain ⟨σ, hσ⟩ := binaryTensorWord_exists_permutation r
    (cast (congrArg BinaryTensorWord h) (binaryTensorStandardPattern m n)) w hc
  exact ⟨σ, rfl, rfl, hσ⟩

/-- 異なる濃度の語は、どの置換でも一致しない。 -/
lemma binaryTensorWord_smul_ne_of_count_ne (r : ℕ) (w z : BinaryTensorWord r)
    (b : Bool) (h : binaryTensorWordCount r w b ≠ binaryTensorWordCount r z b)
    (σ : Equiv.Perm (Fin r)) : σ • w ≠ z := by
  intro he
  apply h
  rw [← binaryTensorWordCount_smul r σ w b, he]

/-- 左の入力数だけで、固定 arity の語の軌道が決まる。 -/
lemma binaryTensorWord_same_count_orbit (r : ℕ) (w z : BinaryTensorWord r)
    (h : binaryTensorWordCount r w false = binaryTensorWordCount r z false) :
    ∃ σ : Equiv.Perm (Fin r), σ • w = z := by
  apply binaryTensorWord_exists_permutation
  intro b
  cases b
  · exact h
  · have hw := binaryTensorWordCount_sum r w
    have hz := binaryTensorWordCount_sum r z
    change binaryTensorWordCount r w true = binaryTensorWordCount r z true
    omega

/-- 指定された個数の左入力を持つ、固定 arity の標準語。 -/
def binaryTensorCountPattern (r : ℕ) (k : Fin (r + 1)) : BinaryTensorWord r :=
  cast (congrArg BinaryTensorWord (Nat.add_sub_of_le (Nat.le_of_lt_succ k.isLt)))
    (binaryTensorStandardPattern k.val (r - k.val))

/-- 固定 arity の標準語の左入力数は、その指定添字。 -/
@[simp]
lemma binaryTensorCountPattern_count (r : ℕ) (k : Fin (r + 1)) :
    binaryTensorWordCount r (binaryTensorCountPattern r k) false = k.val := by
  unfold binaryTensorCountPattern
  rw [binaryTensorWordCount_cast (Nat.add_sub_of_le (Nat.le_of_lt_succ k.isLt))]
  exact binaryTensorStandardPattern_card k.val (r - k.val) false

/-- 固定 arity の任意の語は、その左入力数の標準語の軌道にある。 -/
lemma binaryTensorCountPattern_covers (r : ℕ) (w : BinaryTensorWord r) :
    ∃ (k : Fin (r + 1)) (σ : Equiv.Perm (Fin r)),
      σ • binaryTensorCountPattern r k = w := by
  have hc := binaryTensorWordCount_sum r w
  let k : Fin (r + 1) := ⟨binaryTensorWordCount r w false, by omega⟩
  obtain ⟨σ, hσ⟩ := binaryTensorWord_same_count_orbit r (binaryTensorCountPattern r k) w
    (by rw [binaryTensorCountPattern_count])
  exact ⟨k, σ, hσ⟩

end SerrePositivity.EInfinity
