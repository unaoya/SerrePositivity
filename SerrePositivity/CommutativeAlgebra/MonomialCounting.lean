module

public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Sym.Card
public import Mathlib.SetTheory.Cardinal.NatCard

/-! # 全次数を固定した単項式の数

指数の有限台関数を重複を許す変数の多重集合に移し、次数 `n` の単項式を
`Sym σ n` と同定する。変数が有限個なら、その個数は重複組合せで与えられる。
-/

@[expose] public noncomputable section

namespace SerrePositivity.MonomialCounting

/-- 単項式の指数の全次数は、対応する多重集合の濃度に等しい。 -/
theorem card_toMultiset_eq_degree {σ : Type*} (m : σ →₀ ℕ) :
    m.toMultiset.card = m.degree := by
  rw [Finsupp.card_toMultiset]
  rfl

/-- 多重集合を単項式の指数へ変換すると、全次数は元の濃度になる。 -/
theorem degree_toFinsupp_eq_card {σ : Type*} [DecidableEq σ] (s : Multiset σ) :
    s.toFinsupp.degree = s.card := by
  classical
  change s.toFinsupp.sum (fun _ ↦ id) = s.card
  exact Multiset.toFinsupp_sum_eq s

/-- 次数 `n` の単項式の指数と、`n` 個の変数からなる多重集合との全単射。 -/
def degreeEquivSym (σ : Type*) (n : ℕ) :
    {m : σ →₀ ℕ // m.degree = n} ≃ Sym σ n := by
  classical
  exact {
    toFun := fun m ↦ ⟨m.1.toMultiset, (card_toMultiset_eq_degree m.1).trans m.2⟩
    invFun := fun s ↦ ⟨(s : Multiset σ).toFinsupp,
      (degree_toFinsupp_eq_card (s : Multiset σ)).trans s.2⟩
    left_inv := fun m ↦ Subtype.ext (Finsupp.toMultiset_toFinsupp m.1)
    right_inv := fun s ↦ Sym.ext (Multiset.toFinsupp_toMultiset (s : Multiset σ)) }

/-- 有限個の変数について、次数 `n` の単項式の数は重複組合せである。
サブタイプの `Fintype` は任意のものを使える。 -/
theorem card_degree_eq_multichoose (σ : Type*) [Fintype σ] (n : ℕ)
    [Fintype {m : σ →₀ ℕ // m.degree = n}] :
    Fintype.card {m : σ →₀ ℕ // m.degree = n} =
      Nat.multichoose (Fintype.card σ) n := by
  classical
  rw [Fintype.card_congr (degreeEquivSym σ n), Sym.card_sym_eq_multichoose]

/-- `Nat.card` を使えば、指数サブタイプの `Fintype` を指定する必要がない。 -/
theorem natCard_degree_eq_multichoose (σ : Type*) [Fintype σ] (n : ℕ) :
    Nat.card {m : σ →₀ ℕ // m.degree = n} =
      Nat.multichoose (Fintype.card σ) n := by
  classical
  rw [Nat.card_congr (degreeEquivSym σ n), Nat.card_eq_fintype_card,
    Sym.card_sym_eq_multichoose]

/-- 変数の数も `Nat.card` で表す、有限型に対する形。 -/
theorem natCard_degree_eq_multichoose_of_finite (σ : Type*) [Finite σ] (n : ℕ) :
    Nat.card {m : σ →₀ ℕ // m.degree = n} = Nat.multichoose (Nat.card σ) n := by
  classical
  let : Fintype σ := Fintype.ofFinite σ
  simpa [Nat.card_eq_fintype_card] using natCard_degree_eq_multichoose σ n

end SerrePositivity.MonomialCounting
