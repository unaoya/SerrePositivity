module

public import Mathlib.Algebra.Colimit.Ring
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# 塔 `Λ = lim→ A_n`（論文 (2.1)、Lemma 2.3 (a)）

## 概要

論文 §2.2 の塔 (2.1)：正規化基底 `A`（Lemma 2.2）とその正則パラメータ系 `t = (t₁, …, t_h)`、
剰余標数 `p` について

  `A_n = A[t₁^{1/p^n}, …, t_h^{1/p^n}]`、`Λ = lim→ A_n`（完備化しない）

を具体的に定義する。段 `A_n` は多項式環の商 `A[X₁, …, X_h] / (X_i^{p^n} − t_i)`、遷移写像
`A_a → A_b`（`a ≤ b`）は `X_i ↦ X_i^{p^{b−a}}`、`Λ` は環の直極限（Mathlib `Ring.DirectLimit`）。
混標数で `t₁ = p` の場合もこの形でよい（`p` は `A` の元として扱う）。

論文は「`A_n` は `p` 冪根を固定した代数閉包の中の部分環」として書くが、`A` が正規（正則）なので
`A[X]/(X^{p^n} − t)` と一致する（`X_i^{p^n} − t_i` は Eisenstein 多項式）。この定義にする理由は
`notes/section-2-plan.md` §2：塔を抽象的な存在にすると Theorem 2.5 が偽になるので、`(A, t, p)` から
決まる対象として定義する。

## 内容

- `towerRel`、`TowerStage`、`towerMap`（遷移写像）、`Tower`（`Λ`）と、`A`・各段からの代数構造、
  `IsScalarTower`。
- **Lemma 2.3 (a)** の主張（標準事実）：各段は `A` 上有限生成（整性から証明済み）・自由でランク `p^{nh}`、
  `A_a → A_b` は有限自由でランク `p^{(b−a)h}`、各段は Noether 局所環で剰余体は `k`、正則、完備、
  `Λ` は各段の上で平坦。定義が具体的なので、単項式基底 `X^e`（`0 ≤ e_i < p^n`）と
  `A_n/(X, m_A) = A/(t, m_A) = k` から後で証明できる。
-/

@[expose] public section

universe u

open IsLocalRing MvPolynomial

namespace SerrePositivity

namespace Section2

variable (A : Type u) [CommRing A] {h : ℕ} (t : Fin h → A) (p : ℕ)

/-- 段 `n` の関係式のイデアル `(X_i^{p^n} − t_i)_i ⊆ A[X₁, …, X_h]`。 -/
noncomputable def towerRel (n : ℕ) : Ideal (MvPolynomial (Fin h) A) :=
  Ideal.span (Set.range fun i ↦ (X i : MvPolynomial (Fin h) A) ^ (p ^ n) - C (t i))

/-- 塔の段 `A_n = A[t^{1/p^n}] = A[X₁, …, X_h] / (X_i^{p^n} − t_i)`。 -/
abbrev TowerStage (n : ℕ) : Type u := MvPolynomial (Fin h) A ⧸ towerRel A t p n

/-- 遷移写像の原型 `A[X] → A_b`、`X_i ↦ X_i^{p^{b−a}}`。 -/
noncomputable def towerMapAux (a b : ℕ) : MvPolynomial (Fin h) A →ₐ[A] TowerStage A t p b :=
  (Ideal.Quotient.mkₐ A (towerRel A t p b)).comp
    (aeval fun i ↦ (X i : MvPolynomial (Fin h) A) ^ (p ^ (b - a)))

/-- 関係式 `X_i^{p^a} − t_i` は `A_b` で `0` になる（`a ≤ b`）。 -/
lemma towerMapAux_apply_eq_zero (a b : ℕ) (hab : a ≤ b) (x : MvPolynomial (Fin h) A)
    (hx : x ∈ towerRel A t p a) : towerMapAux A t p a b x = 0 := by
  have hle : towerRel A t p a ≤ RingHom.ker (towerMapAux A t p a b).toRingHom := by
    rw [towerRel, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    have key : towerMapAux A t p a b ((X i : MvPolynomial (Fin h) A) ^ (p ^ a) - C (t i)) =
        Ideal.Quotient.mk (towerRel A t p b)
          ((X i : MvPolynomial (Fin h) A) ^ (p ^ b) - C (t i)) := by
      simp only [towerMapAux, AlgHom.comp_apply, map_sub, map_pow, aeval_X, aeval_C,
        Ideal.Quotient.mkₐ_eq_mk, ← pow_mul, ← pow_add, Nat.sub_add_cancel hab,
        MvPolynomial.algebraMap_eq]
    rw [SetLike.mem_coe, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, key,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span ⟨i, rfl⟩
  exact hle hx

/-- 遷移写像 `A_a → A_b`（`a ≤ b`）、`X_i ↦ X_i^{p^{b−a}}`。 -/
noncomputable def towerMap (a b : ℕ) (hab : a ≤ b) : TowerStage A t p a →ₐ[A] TowerStage A t p b :=
  Ideal.Quotient.liftₐ (towerRel A t p a) (towerMapAux A t p a b)
    (towerMapAux_apply_eq_zero A t p a b hab)

/-- 塔 `Λ = lim→ A_n`（完備化しない）。 -/
noncomputable abbrev Tower : Type u :=
  Ring.DirectLimit (fun n ↦ TowerStage A t p n)
    (fun a b hab ↦ (towerMap A t p a b hab : TowerStage A t p a → TowerStage A t p b))

/-- 段 `A_n` から `Λ` への標準写像。 -/
noncomputable def towerOf (n : ℕ) : TowerStage A t p n →+* Tower A t p :=
  Ring.DirectLimit.of _ _ n

noncomputable instance (n : ℕ) : Algebra (TowerStage A t p n) (Tower A t p) :=
  (towerOf A t p n).toAlgebra

noncomputable instance : Algebra A (Tower A t p) :=
  ((towerOf A t p 0).comp (algebraMap A (TowerStage A t p 0))).toAlgebra

lemma algebraMap_tower_apply (x : A) :
    algebraMap A (Tower A t p) x = towerOf A t p 0 (algebraMap A (TowerStage A t p 0) x) := rfl

lemma algebraMap_towerStage_apply (n : ℕ) (x : TowerStage A t p n) :
    algebraMap (TowerStage A t p n) (Tower A t p) x = towerOf A t p n x := rfl

/-- `towerOf b (towerMap a b x) = towerOf a x`。 -/
lemma towerOf_towerMap (a b : ℕ) (hab : a ≤ b) (x : TowerStage A t p a) :
    towerOf A t p b (towerMap A t p a b hab x) = towerOf A t p a x :=
  Ring.DirectLimit.of_f (G := fun n ↦ TowerStage A t p n) hab x

instance (n : ℕ) : IsScalarTower A (TowerStage A t p n) (Tower A t p) :=
  IsScalarTower.of_algebraMap_eq fun x ↦ by
    rw [algebraMap_tower_apply, algebraMap_towerStage_apply,
      ← towerOf_towerMap A t p 0 n (Nat.zero_le n), AlgHom.commutes]

/-- `Λ` の元はどれかの段から来る。 -/
lemma exists_towerOf (z : Tower A t p) :
    ∃ (n : ℕ) (x : TowerStage A t p n), towerOf A t p n x = z :=
  Ring.DirectLimit.exists_of z

/-- `m_A Λ`：Lemma 2.3 の `λ_∞` の加法性の定義域を定めるイデアル。 -/
noncomputable abbrev towerMaxIdeal [IsLocalRing A] : Ideal (Tower A t p) :=
  (maximalIdeal A).map (algebraMap A (Tower A t p))

/-- 段 `n` の正規化の分母 `s(n) = p^{nh} = rank_A A_n`（Lemma 5.4 の `s(j)`）。 -/
def stageRank (h p n : ℕ) : ℕ := p ^ (n * h)

/-! ## Lemma 2.3 (a)：段の性質（標準事実、`sorry`）

単項式 `X^e`（`0 ≤ e_i < p^n`）が `A_n` の `A` 上の基底であること、`A_n / (X, m_A) = A/(t, m_A) = k`
から局所性と剰余体、`A` 上有限なので完備、`A_n` の極大イデアルが `h` 個の元 `X_i` で生成されること
から正則性が出る。いずれも標準的な議論だが、ここでは主張だけ置く。 -/

section facts

/-- `X_i` の像は `A` 上整：`X_i^{p^n} = t_i`。 -/
lemma isIntegral_towerStage_X [Fact p.Prime] (n : ℕ) (i : Fin h) :
    IsIntegral A (Ideal.Quotient.mkₐ A (towerRel A t p n) (X i)) := by
  have hpow : Ideal.Quotient.mkₐ A (towerRel A t p n) (X i) ^ (p ^ n) =
      algebraMap A (TowerStage A t p n) (t i) := by
    rw [← map_pow, ← AlgHom.commutes (Ideal.Quotient.mkₐ A (towerRel A t p n)),
      MvPolynomial.algebraMap_eq]
    simp only [Ideal.Quotient.mkₐ_eq_mk]
    rw [Ideal.Quotient.eq]
    exact Ideal.subset_span ⟨i, rfl⟩
  refine IsIntegral.of_pow (pow_pos (Fact.out : p.Prime).pos n) ?_
  rw [hpow]
  exact isIntegral_algebraMap

/-- 各段は `A` 上整：`X_i` の像で生成され、各 `X_i` は整。 -/
theorem isIntegral_towerStage [Fact p.Prime] (n : ℕ) :
    Algebra.IsIntegral A (TowerStage A t p n) := by
  rw [← integralClosure_eq_top_iff, eq_top_iff]
  have hadj : Algebra.adjoin A
      (Set.range fun i ↦ Ideal.Quotient.mkₐ A (towerRel A t p n) (X i)) = ⊤ := by
    rw [Set.range_comp' (Ideal.Quotient.mkₐ A (towerRel A t p n)), Algebra.adjoin_image,
      MvPolynomial.adjoin_range_X, Algebra.map_top, AlgHom.range_eq_top]
    exact Ideal.Quotient.mkₐ_surjective A _
  rw [← hadj]
  refine Algebra.adjoin_le ?_
  rintro _ ⟨i, rfl⟩
  exact isIntegral_towerStage_X A t p n i

/-- 各段は `A` 上有限生成（有限型かつ整）。 -/
theorem towerStage_finite [Fact p.Prime] (n : ℕ) : Module.Finite A (TowerStage A t p n) := by
  have : Algebra.FiniteType A (TowerStage A t p n) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ A (towerRel A t p n))
      (Ideal.Quotient.mkₐ_surjective A _)
  have := isIntegral_towerStage A t p n
  exact Algebra.IsIntegral.finite

/-- 各段は `A` 上有限自由（単項式 `X^e`、`0 ≤ e_i < p^n` が基底）。 -/
theorem towerStage_free [Fact p.Prime] (n : ℕ) : Module.Free A (TowerStage A t p n) := by
  sorry

/-- 各段のランクは `p^{nh}`。 -/
theorem finrank_towerStage [Nontrivial A] [Fact p.Prime] (n : ℕ) :
    Module.finrank A (TowerStage A t p n) = stageRank h p n := by
  sorry

/-- `A_a → A_b` は有限自由でランク `p^{(b−a)h}`。 -/
theorem towerMap_free_finrank [Nontrivial A] [Fact p.Prime] (a b : ℕ) (hab : a ≤ b) :
    letI := (towerMap A t p a b hab).toRingHom.toAlgebra
    Module.Free (TowerStage A t p a) (TowerStage A t p b) ∧
      Module.Finite (TowerStage A t p a) (TowerStage A t p b) ∧
      Module.finrank (TowerStage A t p a) (TowerStage A t p b) = stageRank h p (b - a) := by
  sorry

/-- 各段は Noether 環（多項式環の商）。 -/
instance isNoetherianRing_towerStage [IsNoetherianRing A] (n : ℕ) :
    IsNoetherianRing (TowerStage A t p n) :=
  inferInstance

/-- 各段は正則局所環（`A` が正則で `t` が正則パラメータ系のとき）。 -/
theorem isRegularLocalRing_towerStage [IsRegularLocalRing A]
    (ht' : Ideal.span (Set.range t) = maximalIdeal A) (hdim : ringKrullDim A = h) (n : ℕ) :
    IsRegularLocalRing (TowerStage A t p n) := by
  sorry

variable [IsLocalRing A] (ht : ∀ i, t i ∈ maximalIdeal A)

include ht in
/-- 各段は局所環（`X_i` は `m_A A_n` の上で冪零なので、極大イデアルは `(X, m_A)` だけ）。 -/
theorem isLocalRing_towerStage (n : ℕ) : IsLocalRing (TowerStage A t p n) := by
  sorry

include ht in
/-- 各段の剰余体は `k`：`A → A_n → A_n/m` は全射。 -/
theorem residue_surjective_towerStage (n : ℕ) :
    haveI := isLocalRing_towerStage A t p ht n
    Function.Surjective
      ((residue (TowerStage A t p n)).comp (algebraMap A (TowerStage A t p n))) := by
  sorry

include ht in
/-- 各段は完備（`A` が完備で `A_n` が `A` 上有限のとき）。 -/
theorem isAdicComplete_towerStage [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A] (n : ℕ) :
    haveI := isLocalRing_towerStage A t p ht n
    IsAdicComplete (maximalIdeal (TowerStage A t p n)) (TowerStage A t p n) := by
  sorry

/-- `Λ` は各段の上で平坦（自由加群の有向極限）。Lemma 5.4 で `Tor` を段に降ろすのに使う。 -/
theorem flat_tower (n : ℕ) : Module.Flat (TowerStage A t p n) (Tower A t p) := by
  sorry

end facts

end Section2

end SerrePositivity
