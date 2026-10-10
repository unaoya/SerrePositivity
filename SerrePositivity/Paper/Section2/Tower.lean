module

public import SerrePositivity.Paper.Section2.MonomialBasis
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
- Lemma 2.3 (a)（段の性質：有限自由とランク、局所性と剰余体、正則性、完備性、平坦性）は
  `Paper/Section2/TowerStage.lean`。
-/

@[expose] public section

universe u

open IsLocalRing MvPolynomial

namespace SerrePositivity

namespace Section2

variable (A : Type u) [CommRing A] {h : ℕ} (t : Fin h → A) (p : ℕ)

/-- 段 `n` の関係式のイデアル `(X_i^{p^n} − t_i)_i ⊆ A[X₁, …, X_h]`（`MonomialBasis.lean` の
`relIdeal` で `q = p^n`）。 -/
noncomputable def towerRel (n : ℕ) : Ideal (MvPolynomial (Fin h) A) := relIdeal A t (p ^ n)

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
    rw [towerRel, relIdeal, Ideal.span_le]
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

/-- `towerMap a b (X_i) = X_i^{p^{b−a}}`。 -/
lemma towerMap_mk_X (a b : ℕ) (hab : a ≤ b) (i : Fin h) :
    towerMap A t p a b hab (Ideal.Quotient.mk (towerRel A t p a) (X i)) =
      Ideal.Quotient.mk (towerRel A t p b) (X i) ^ (p ^ (b - a)) := by
  change towerMapAux A t p a b (X i) = _
  simp only [towerMapAux, AlgHom.comp_apply, aeval_X, Ideal.Quotient.mkₐ_eq_mk, map_pow]

/-- `towerMap a a = id`。 -/
lemma towerMap_self (a : ℕ) (x : TowerStage A t p a) : towerMap A t p a a le_rfl x = x := by
  have : towerMap A t p a a le_rfl = AlgHom.id A _ := by
    refine Ideal.Quotient.algHom_ext A ?_
    refine MvPolynomial.algHom_ext fun i ↦ ?_
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, AlgHom.id_apply]
    rw [towerMap_mk_X, Nat.sub_self, pow_zero, pow_one]
  exact AlgHom.congr_fun this x

/-- `towerMap b c ∘ towerMap a b = towerMap a c`。 -/
lemma towerMap_towerMap (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) (x : TowerStage A t p a) :
    towerMap A t p b c hbc (towerMap A t p a b hab x) = towerMap A t p a c (hab.trans hbc) x := by
  have : (towerMap A t p b c hbc).comp (towerMap A t p a b hab) =
      towerMap A t p a c (hab.trans hbc) := by
    refine Ideal.Quotient.algHom_ext A ?_
    refine MvPolynomial.algHom_ext fun i ↦ ?_
    have hc : p ^ (c - b) * p ^ (b - a) = p ^ (c - a) := by
      rw [← pow_add]
      congr 1
      omega
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
    rw [towerMap_mk_X, map_pow, towerMap_mk_X, ← pow_mul, hc, towerMap_mk_X]
  exact AlgHom.congr_fun this x

/-- 遷移写像（環準同型として）。`Ring.DirectLimit` とその `of.zero_exact` はこの形で使う。 -/
noncomputable def towerMapRingHom (a b : ℕ) (hab : a ≤ b) :
    TowerStage A t p a →+* TowerStage A t p b :=
  (towerMap A t p a b hab).toRingHom

lemma towerMapRingHom_apply (a b : ℕ) (hab : a ≤ b) (x : TowerStage A t p a) :
    towerMapRingHom A t p a b hab x = towerMap A t p a b hab x := rfl

/-- 段と遷移写像は有向系をなす。 -/
instance : DirectedSystem (fun n ↦ TowerStage A t p n)
    fun a b hab ↦ ⇑(towerMapRingHom A t p a b hab) where
  map_self _ x := towerMap_self A t p _ x
  map_map _ _ _ hab hbc x := towerMap_towerMap A t p _ _ _ hab hbc x

/-- 塔 `Λ = lim→ A_n`（完備化しない）。 -/
noncomputable abbrev Tower : Type u :=
  Ring.DirectLimit (fun n ↦ TowerStage A t p n) fun a b hab ↦ ⇑(towerMapRingHom A t p a b hab)

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
    towerOf A t p b (towerMap A t p a b hab x) = towerOf A t p a x := by
  rw [← towerMapRingHom_apply]
  exact Ring.DirectLimit.of_f (G := fun n ↦ TowerStage A t p n) hab x

instance (n : ℕ) : IsScalarTower A (TowerStage A t p n) (Tower A t p) :=
  IsScalarTower.of_algebraMap_eq fun x ↦ by
    rw [algebraMap_tower_apply, algebraMap_towerStage_apply,
      ← towerOf_towerMap A t p 0 n (Nat.zero_le n), AlgHom.commutes]

/-- `Λ` の元はどれかの段から来る。 -/
lemma exists_towerOf (z : Tower A t p) :
    ∃ (n : ℕ) (x : TowerStage A t p n), towerOf A t p n x = z :=
  Ring.DirectLimit.exists_of z

/-- `Λ` の有限個の元は共通の段から来る。 -/
lemma exists_towerOf_family {ι : Type*} [Finite ι] (w : ι → Tower A t p) :
    ∃ (m : ℕ) (z : ι → TowerStage A t p m), ∀ i, towerOf A t p m (z i) = w i := by
  cases nonempty_fintype ι
  choose ms zs hzs using fun i ↦ exists_towerOf A t p (w i)
  refine ⟨Finset.univ.sup ms, fun i ↦
    towerMap A t p (ms i) _ (Finset.le_sup (Finset.mem_univ i)) (zs i), fun i ↦ ?_⟩
  rw [towerOf_towerMap, hzs]

/-- 段 `m` の有限個の元が `Λ` で `0` なら、ある段 `m' ≥ m` ですでに `0`。 -/
lemma exists_towerMap_eq_zero {ι : Type*} [Finite ι] (m : ℕ) (z : ι → TowerStage A t p m)
    (hz : ∀ i, towerOf A t p m (z i) = 0) :
    ∃ (m' : ℕ) (hmm' : m ≤ m'), ∀ i, towerMap A t p m m' hmm' (z i) = 0 := by
  cases nonempty_fintype ι
  choose ms hms hz' using fun i ↦ Ring.DirectLimit.of.zero_exact
    (G := fun n ↦ TowerStage A t p n) (f' := towerMapRingHom A t p) (hz i)
  refine ⟨m ⊔ Finset.univ.sup ms, le_sup_left, fun i ↦ ?_⟩
  rw [← towerMap_towerMap A t p m (ms i) _ (hms i)
    (le_sup_of_le_right (Finset.le_sup (Finset.mem_univ i))),
    show towerMap A t p m (ms i) (hms i) (z i) = 0 from hz' i, map_zero]

/-- `m_A Λ`：Lemma 2.3 の `λ_∞` の加法性の定義域を定めるイデアル。 -/
noncomputable abbrev towerMaxIdeal [IsLocalRing A] : Ideal (Tower A t p) :=
  (maximalIdeal A).map (algebraMap A (Tower A t p))

/-- 段 `n` の正規化の分母 `s(n) = p^{nh} = rank_A A_n`（Lemma 5.4 の `s(j)`）。 -/
def stageRank (h p n : ℕ) : ℕ := p ^ (n * h)


end Section2

end SerrePositivity
