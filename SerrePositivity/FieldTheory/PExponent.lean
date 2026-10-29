module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Finsupp.Option
public import Mathlib.Logic.Equiv.Sum

/-! # p 指数と p 単項式

概要：各成分が `p` 未満の有限台の指数 `PExponent p ι` と、族 `b` の p 単項式 `bᵈ = Π bᵢ^{dᵢ}`。
指数の操作（零延長・一点・`Option` と直和での分解・`p q` 進の桁分解・`p` で割った余り）と、単項式の対応する計算規則。
方針：指数は ℕ 値の有限台関数の部分型で持ち、上界は証明として持つ（単項式の積で指数が `p` を超える計算を
ℕ の中で行うため）。Mathlib の `Finsupp` の同値（`optionEquiv`・`sumFinsuppEquivProdFinsupp`・
`equivFunOnFinite`）を上界つきに持ち上げ、`Fin p` 値の有限台関数との同値 `equivFinsupp` も置く。
規約：添字集合の有限性は、個数の公式と `ι → Fin p` との同値にだけ使う。標数の仮定は使わない。
使われ方：p 基底（`PBasis`）、Frobenius 塔の単項式基底、補中間体の単項式基底。
-/

@[expose] public section
namespace SerrePositivity

/-- 各成分が `p` 未満の有限台指数。 -/
abbrev PExponent (p : ℕ) (ι : Type*) := {d : ι →₀ ℕ // ∀ i, d i < p}

namespace PExponent

variable {p : ℕ} {ι κ : Type*}

instance [NeZero p] : Zero (PExponent p ι) :=
  ⟨⟨0, fun _ ↦ Nat.pos_of_ne_zero (NeZero.ne p)⟩⟩

/-- 添字の埋め込みに沿って指数を零で延長する。 -/
noncomputable def embDomain [NeZero p] (e : ι ↪ κ) (d : PExponent p ι) :
    PExponent p κ := by
  classical
  refine ⟨d.val.embDomain e, fun i ↦ ?_⟩
  by_cases hi : ∃ j, e j = i
  · obtain ⟨j, rfl⟩ := hi
    simpa using d.property j
  · rw [Finsupp.embDomain_of_notMem_range e d.val i hi]
    exact Nat.pos_of_ne_zero (NeZero.ne p)

theorem embDomain_injective [NeZero p] (e : ι ↪ κ) :
    Function.Injective (embDomain (p := p) e) := by
  intro d d' h
  apply Subtype.ext
  exact Finsupp.embDomain_injective e (congrArg Subtype.val h)

/-- 有限添字に限れば、有限台指数は `Fin p` 値の関数と同じ。 -/
noncomputable def equivFin [Finite ι] : PExponent p ι ≃ (ι → Fin p) where
  toFun d i := ⟨d.val i, d.property i⟩
  invFun f := ⟨Finsupp.equivFunOnFinite.symm (fun i ↦ (f i).val), fun i ↦ (f i).isLt⟩
  left_inv d := by
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    rfl
  right_inv f := by
    funext i
    rfl

noncomputable instance [Fintype ι] : Fintype (PExponent p ι) := by
  classical
  exact Fintype.ofEquiv (ι → Fin p) equivFin.symm

theorem card [Fintype ι] : Fintype.card (PExponent p ι) = p ^ Fintype.card ι := by
  classical
  rw [Fintype.card_congr equivFin]
  simp

/-- 一つの変数だけに指定指数を置く。 -/
noncomputable def single (i : ι) (n : Fin p) : PExponent p ι := by
  classical
  refine ⟨Finsupp.single i n.val, fun j ↦ ?_⟩
  by_cases h : i = j
  · subst j
    simp
  · simpa [Finsupp.single_apply, h, Ne.symm h] using Nat.zero_lt_of_lt n.isLt

/-- 新しい一つの添字の指数と、既存添字の指数を分ける。 -/
noncomputable def splitOption (d : PExponent p (Option ι)) : PExponent p ι × Fin p :=
  (⟨d.val.some, fun i ↦ d.property (some i)⟩, ⟨d.val none, d.property none⟩)

/-- `Option ι` 上の指数を、既存の添字の指数と新しい添字の指数に分ける同値
（逆写像は Mathlib の `Finsupp.optionElim`）。 -/
noncomputable def optionEquiv : PExponent p (Option ι) ≃ PExponent p ι × Fin p where
  toFun := splitOption
  invFun z := ⟨z.1.val.optionElim z.2.val, fun i ↦ by
    cases i with
    | none => simp
    | some i => simpa using z.1.property i⟩
  left_inv d := by
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    cases i <;> simp [splitOption]
  right_inv z := by
    apply Prod.ext
    · apply Subtype.ext; apply Finsupp.ext; intro i; simp [splitOption]
    · apply Fin.ext; simp [splitOption]

theorem splitOption_injective : Function.Injective (splitOption (p := p) (ι := ι)) :=
  optionEquiv.injective

/-- 指数の型は、`Fin p` 値の有限台関数と同じ（添字の有限性は不要）。 -/
noncomputable def equivFinsupp [NeZero p] : PExponent p ι ≃ (ι →₀ Fin p) where
  toFun d := Finsupp.onFinset d.val.support (fun i ↦ ⟨d.val i, d.property i⟩) fun i h ↦ by
    simpa [Fin.ext_iff] using h
  invFun f := ⟨f.mapRange Fin.val (Fin.val_zero p), fun i ↦ (f i).isLt⟩
  left_inv d := by
    apply Subtype.ext; apply Finsupp.ext; intro i; rfl
  right_inv f := by
    apply Finsupp.ext; intro i; rfl

end PExponent

/-- 族 `b` の有限台 p 単項式。 -/
noncomputable def pMonomial {p : ℕ} {ι K : Type*} [CommMonoid K]
    (b : ι → K) (d : PExponent p ι) : K :=
  d.val.prod (fun i n ↦ b i ^ n)

@[simp] theorem pMonomial_zero {p : ℕ} {ι K : Type*} [NeZero p] [CommMonoid K]
    (b : ι → K) : pMonomial b (0 : PExponent p ι) = 1 := by
  change (0 : ι →₀ ℕ).prod (fun i n ↦ b i ^ n) = 1
  simp

@[simp] theorem pMonomial_single {p : ℕ} {ι K : Type*} [CommMonoid K]
    (b : ι → K) (i : ι) (n : Fin p) :
    pMonomial b (PExponent.single i n) = b i ^ n.val := by
  exact Finsupp.prod_single_index (pow_zero _)

/-- 部分族の単項式は、指数を零で延長した元の族の単項式に一致する。 -/
theorem pMonomial_embDomain {p : ℕ} {ι κ K : Type*} [NeZero p] [CommMonoid K]
    (b : κ → K) (e : ι ↪ κ) (d : PExponent p ι) :
    pMonomial b (PExponent.embDomain e d) = pMonomial (b ∘ e) d := by
  exact Finsupp.prod_embDomain

/-- 一つの元を添加した族の単項式を、既存の単項式と新しい元の冪に分解する。 -/
theorem pMonomial_optionElim {p : ℕ} {ι K : Type*} [CommMonoid K]
    (b : ι → K) (x : K) (d : PExponent p (Option ι)) :
    pMonomial (Option.elim' x b) d =
      pMonomial b (PExponent.splitOption d).1 * x ^ (PExponent.splitOption d).2.val := by
  rw [pMonomial, Finsupp.prod_option_index _ _ (by intro i; simp)
    (by intro i m n; exact pow_add _ _ _)]
  exact mul_comm _ _

/-- p 単項式の独立性は任意の部分族へ制限できる。 -/
theorem linearIndependent_pMonomial_comp
    {p : ℕ} {ι κ F K : Type*} [NeZero p] [Field F] [Field K] [Algebra F K]
    {b : κ → K} (hb : LinearIndependent F (pMonomial (p := p) b)) (e : ι ↪ κ) :
    LinearIndependent F (pMonomial (p := p) (b ∘ e)) := by
  have h := hb.comp (PExponent.embDomain e) (PExponent.embDomain_injective e)
  simpa only [Function.comp_def, pMonomial_embDomain] using h

/-- 有限族の独立な p 単項式が張る空間の次元は `p ^ |ι|`。 -/
theorem finrank_span_pMonomial
    {p : ℕ} {ι F K : Type*} [Fintype ι] [Field F] [Field K] [Algebra F K]
    {b : ι → K} (hb : LinearIndependent F (pMonomial (p := p) b)) :
    Module.finrank F (Submodule.span F (Set.range (pMonomial (p := p) b))) =
      p ^ Fintype.card ι := by
  rw [finrank_span_eq_card hb, PExponent.card]

section Radix

namespace PExponent

variable {ι : Type*} (p q : ℕ) [NeZero q]

/-- q を基数とした、高い桁と低い桁。 -/
noncomputable def radixSplit (d : PExponent (p * q) ι) : PExponent p ι × PExponent q ι :=
  (⟨d.val.mapRange (fun a ↦ a / q) (Nat.zero_div q), fun i ↦
      (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero (NeZero.ne q))).mpr (d.property i)⟩,
    ⟨d.val.mapRange (fun a ↦ a % q) (Nat.zero_mod q), fun _ ↦
      Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne q))⟩)

/-- 高い桁に q を掛けて低い桁を加える。 -/
noncomputable def radixJoin (d : PExponent p ι × PExponent q ι) : PExponent (p * q) ι :=
  ⟨d.1.val.mapRange (fun a ↦ a * q) (Nat.zero_mul q) + d.2.val, fun i ↦ by
    change d.1.val i * q + d.2.val i < p * q
    have h₁ := d.1.property i
    have h₂ := d.2.property i
    calc
      d.1.val i * q + d.2.val i < d.1.val i * q + q := Nat.add_lt_add_left h₂ _
      _ = (d.1.val i + 1) * q := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ p * q := Nat.mul_le_mul_right q (by omega)⟩

/-- 商・余りによる有限台指数の同値。 -/
noncomputable def radixEquiv : PExponent (p * q) ι ≃ PExponent p ι × PExponent q ι where
  toFun := radixSplit p q
  invFun := radixJoin p q
  left_inv d := by
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    change d.val i / q * q + d.val i % q = d.val i
    exact Nat.div_add_mod' _ _
  right_inv d := by
    apply Prod.ext <;> apply Subtype.ext <;> apply Finsupp.ext <;> intro i
    · change (d.1.val i * q + d.2.val i) / q = d.1.val i
      have h := d.2.property i
      rw [Nat.mul_comm (d.1.val i) q,
        Nat.mul_add_div (Nat.pos_of_ne_zero (NeZero.ne q)), Nat.div_eq_of_lt h,
        Nat.add_zero]
    · change (d.1.val i * q + d.2.val i) % q = d.2.val i
      simp [Nat.add_mod, Nat.mod_eq_of_lt (d.2.property i)]

end PExponent

/-- 桁の結合は単項式の積に対応する。標数の仮定は不要。 -/
theorem pMonomial_radixJoin {ι k : Type*} [CommMonoid k] (p q : ℕ) [NeZero q]
    (b : ι → k) (d : PExponent p ι × PExponent q ι) :
    pMonomial b (PExponent.radixJoin p q d) = (pMonomial b d.1) ^ q * pMonomial b d.2 := by
  rw [pMonomial, PExponent.radixJoin,
    Finsupp.prod_add_index' (by intro i; simp) (by intro i a c; exact pow_add _ _ _),
    Finsupp.prod_mapRange_index (by intro i; simp)]
  simp only [pMonomial, pow_mul, Finsupp.prod, Finset.prod_pow]

end Radix

section Remainder

/-- 有限台指数の各成分を `p` で割った余り（上界のない指数の低い桁）。 -/
noncomputable def PExponent.remainder {ι : Type*} (p : ℕ) [NeZero p] (d : ι →₀ ℕ) :
    PExponent p ι :=
  ⟨d.mapRange (fun n ↦ n % p) (Nat.zero_mod p),
    fun _ ↦ Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne p))⟩

/-- 任意の単項式は、`p` 乗の因子と指数 `p` 未満の単項式の積に分かれる。 -/
theorem finsuppMonomial_eq_pow_mul_remainder
    {ι K : Type*} [CommMonoid K] (p : ℕ) [NeZero p] (b : ι → K) (d : ι →₀ ℕ) :
    d.prod (fun i n ↦ b i ^ n) =
      (d.prod (fun i n ↦ b i ^ (n / p))) ^ p *
        pMonomial b (PExponent.remainder p d) := by
  classical
  rw [pMonomial, PExponent.remainder,
    Finsupp.prod_mapRange_index (by intro i; simp)]
  simp only [Finsupp.prod, ← Finset.prod_pow, ← Finset.prod_mul_distrib, ← pow_mul,
    ← pow_add, Nat.div_add_mod']

end Remainder

section Partition

namespace PExponent


/-- 直和上の有限台p指数を二つの成分へ分ける同値（Mathlib の `Finsupp.sumFinsuppEquivProdFinsupp` を
指数の上界つきに持ち上げたもの）。添字の有限性は不要。 -/
noncomputable def sumEquiv {p : ℕ} {ι κ : Type*} :
    PExponent p (ι ⊕ κ) ≃ PExponent p ι × PExponent p κ :=
  (Equiv.subtypeEquiv (p := fun d : ι ⊕ κ →₀ ℕ ↦ ∀ i, d i < p)
    (q := fun x : (ι →₀ ℕ) × (κ →₀ ℕ) ↦ (∀ i, x.1 i < p) ∧ ∀ i, x.2 i < p)
    Finsupp.sumFinsuppEquivProdFinsupp fun d ↦ by simp [Sum.forall]).trans
    (Equiv.subtypeProdEquivProd (α := ι →₀ ℕ) (β := κ →₀ ℕ) (p := fun f ↦ ∀ i, f i < p)
      (q := fun f ↦ ∀ i, f i < p))

/-- 直和の二つの成分の有限台指数を合成する（`sumEquiv` の逆）。 -/
noncomputable def sumElim {p : ℕ} {ι κ : Type*}
    (d : PExponent p ι) (e : PExponent p κ) : PExponent p (ι ⊕ κ) :=
  sumEquiv.symm (d, e)

theorem sumElim_injective {p : ℕ} {ι κ : Type*} :
    Function.Injective (fun z : PExponent p ι × PExponent p κ ↦ sumElim z.1 z.2) :=
  sumEquiv.symm.injective

/-- 補集合と元の集合の指数を、元の添字上の指数へ合成する。 -/
noncomputable def combinePartition {p : ℕ} [NeZero p] {ι : Type*} (s : Set ι)
    (z : PExponent p s × PExponent p {i // i ∉ s}) : PExponent p ι := by
  classical
  exact embDomain (Equiv.sumCompl (· ∈ s)).toEmbedding (sumElim z.1 z.2)

theorem combinePartition_injective {p : ℕ} [NeZero p] {ι : Type*} (s : Set ι) :
    Function.Injective (combinePartition (p := p) s) := by
  classical
  exact (embDomain_injective (Equiv.sumCompl (· ∈ s)).toEmbedding).comp sumElim_injective


end PExponent

theorem pMonomial_sumElim {p : ℕ} {ι κ K : Type*} [CommMonoid K]
    (b : ι ⊕ κ → K) (d : PExponent p ι) (e : PExponent p κ) :
    pMonomial b (PExponent.sumElim d e) =
      pMonomial (b ∘ Sum.inl) d * pMonomial (b ∘ Sum.inr) e := by
  change ((Finsupp.sumElim d.val e.val).prod fun i n ↦ b i ^ n) = _
  exact Finsupp.prod_sumElim d.val e.val _

/-- 補集合の単項式と残した方向の単項式の積は、元の族の一つの単項式。 -/
theorem pMonomial_combinePartition {p : ℕ} [NeZero p] {ι K : Type*} [CommMonoid K]
    (b : ι → K) (s : Set ι)
    (z : PExponent p s × PExponent p {i // i ∉ s}) :
    pMonomial b (PExponent.combinePartition s z) =
      pMonomial (fun i : s ↦ b i) z.1 *
        pMonomial (fun i : {i // i ∉ s} ↦ b i) z.2 := by
  classical
  rw [PExponent.combinePartition, pMonomial_embDomain, pMonomial_sumElim]
  rfl

end Partition

end SerrePositivity
