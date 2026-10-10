module

public import SerrePositivity.Paper.Section2.Tower
public import SerrePositivity.CommutativeAlgebra.AdicCompleteness
public import SerrePositivity.CommutativeAlgebra.IntegralDimension
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# 塔の段の性質（論文 Lemma 2.3 (a)）

## 概要

塔の段 `A_n = A[X₁, …, X_h]/(X_i^{p^n} − t_i)`（`Paper/Section2/Tower.lean`）について、
論文 Lemma 2.3 (a) の主張：各段は完備正則局所環で剰余体は `k`、`A_a → A_b` は有限自由で
ランク `p^{(b−a)h}`（とくに `A → A_n` はランク `p^{nh}`）。加えて Lemma 5.4 で使う
「`Λ` は各段の上で平坦」。

## 内容

- 単項式基底（`MonomialBasis.lean`）から：各段は `A` 上有限自由でランク `p^{nh}`
  （`towerStage_free`、`towerStage_finite`、`finrank_towerStage`、基底 `towerStageBasis`）。
- 整性：`X_i^{p^n} = t_i`（`isIntegral_towerStage`）。各段は Noether 環（`A` が Noether なら）。
- 段間の有限自由性とランク、局所性と剰余体、`Λ` の平坦性を証明する。
- 完備性は有限な局所環拡大の一般論、正則性は整拡大の次元保存と極大イデアルの生成元数から導く。
  このファイルの主張はすべて `sorry` に依存しない。
-/

@[expose] public section

universe u

open IsLocalRing MvPolynomial

namespace SerrePositivity

namespace Section2

variable (A : Type u) [CommRing A] {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]

lemma pow_pos_of_prime (n : ℕ) : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n

/-! ## 有限自由とランク -/

/-- 各段の単項式基底 `X^e`（`0 ≤ e_i < p^n`）。 -/
noncomputable def towerStageBasis (n : ℕ) :
    Module.Basis (Fin h → Fin (p ^ n)) A (TowerStage A t p n) :=
  relBasis A t (p ^ n) (pow_pos_of_prime p n)

/-- 各段は `A` 上自由。 -/
theorem towerStage_free (n : ℕ) : Module.Free A (TowerStage A t p n) :=
  free_quotient_relIdeal A t (p ^ n) (pow_pos_of_prime p n)

/-- 各段は `A` 上有限生成。 -/
theorem towerStage_finite (n : ℕ) : Module.Finite A (TowerStage A t p n) :=
  finite_quotient_relIdeal A t (p ^ n) (pow_pos_of_prime p n)

/-- 各段のランクは `p^{nh}`。 -/
theorem finrank_towerStage [Nontrivial A] (n : ℕ) :
    Module.finrank A (TowerStage A t p n) = stageRank h p n := by
  rw [stageRank, pow_mul]
  exact finrank_quotient_relIdeal A t (p ^ n) (pow_pos_of_prime p n)

/-! ## 整性 -/

omit [Fact p.Prime] in
/-- `X_i` の像の `p^n` 乗は `t_i`。 -/
lemma mk_X_pow (n : ℕ) (i : Fin h) :
    Ideal.Quotient.mk (towerRel A t p n) (X i) ^ (p ^ n) =
      algebraMap A (TowerStage A t p n) (t i) := by
  change Ideal.Quotient.mk _ (X i) ^ (p ^ n) =
    Ideal.Quotient.mk _ (C (t i))
  rw [← map_pow, Ideal.Quotient.eq]
  exact Ideal.subset_span ⟨i, rfl⟩

/-- `X_i` の像は `A` 上整：`X_i^{p^n} = t_i`。 -/
lemma isIntegral_towerStage_X (n : ℕ) (i : Fin h) :
    IsIntegral A (Ideal.Quotient.mk (towerRel A t p n) (X i)) := by
  refine IsIntegral.of_pow (pow_pos_of_prime p n) ?_
  rw [mk_X_pow]
  exact isIntegral_algebraMap

/-- 各段は `A` 上整：`X_i` の像で生成され、各 `X_i` は整。 -/
theorem isIntegral_towerStage (n : ℕ) : Algebra.IsIntegral A (TowerStage A t p n) := by
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

/-- 各段は Noether 環（多項式環の商）。 -/
instance isNoetherianRing_towerStage [IsNoetherianRing A] (n : ℕ) :
    IsNoetherianRing (TowerStage A t p n) :=
  inferInstance

/-! ## 遷移写像の自由性とランク

`A_b = A_a[Y₁, …, Y_h]/(Y_i^{p^{b−a}} − x_i)`（`x_i` は `A_a` での `X_i` の像）なので、
`MonomialBasis.lean` の一般論を `A_a` 上で使う。同型は `Y_i ↦ X_i` で、逆は `X_i ↦ Y_i`。 -/

/-- 代数準同型 `φ : R[X] → B` が `φ(X_i)^q = s_i` をみたすなら `relIdeal R s q` を消す。 -/
lemma relIdeal_apply_eq_zero {R B : Type*} [CommRing R] [CommRing B] [Algebra R B] {h : ℕ}
    (s : Fin h → R) (q : ℕ) (φ : MvPolynomial (Fin h) R →ₐ[R] B)
    (hφ : ∀ i, φ (X i) ^ q = algebraMap R B (s i)) :
    ∀ f ∈ relIdeal R s q, φ f = 0 := by
  intro f hf
  have hle : relIdeal R s q ≤ RingHom.ker φ.toRingHom := by
    rw [relIdeal, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, map_sub,
      map_pow, hφ, ← MvPolynomial.algebraMap_eq, AlgHom.commutes, sub_self]
  exact hle hf

section relative

variable (a b : ℕ) (hab : a ≤ b)

/-- `A_a` での `X_i` の像 `x_i`。 -/
noncomputable abbrev stageX (a : ℕ) (i : Fin h) : TowerStage A t p a :=
  Ideal.Quotient.mk (towerRel A t p a) (X i)

/-- `A_a` 上の相対的な段 `A_a[Y]/(Y_i^{p^{b−a}} − x_i)`。 -/
noncomputable abbrev RelStage : Type u :=
  MvPolynomial (Fin h) (TowerStage A t p a) ⧸
    relIdeal (TowerStage A t p a) (stageX A t p a) (p ^ (b - a))

omit [Fact p.Prime] in
/-- `towerMap a b (x_i) = X_i^{p^{b−a}}`。 -/
lemma towerMap_stageX (i : Fin h) :
    towerMap A t p a b hab (stageX A t p a i) =
      Ideal.Quotient.mk (towerRel A t p b) (X i ^ (p ^ (b - a))) := by
  rw [towerMap_mk_X, map_pow]

omit [Fact p.Prime] in
/-- 相対的な段で `Y_i^{p^{b−a}} = x_i`。 -/
lemma mk_Y_pow (i : Fin h) :
    Ideal.Quotient.mk (relIdeal (TowerStage A t p a) (stageX A t p a) (p ^ (b - a))) (X i) ^
        (p ^ (b - a)) =
      algebraMap (TowerStage A t p a) (RelStage A t p a b) (stageX A t p a i) := by
  change Ideal.Quotient.mk _ (X i) ^ (p ^ (b - a)) =
    Ideal.Quotient.mk _ (C (stageX A t p a i))
  rw [← map_pow, Ideal.Quotient.eq]
  exact Ideal.subset_span ⟨i, rfl⟩

/-- 相対的な段から `A_b` へ：`Y_i ↦ X_i`、`A_a` は `towerMap` で。 -/
noncomputable def relStageTo :
    letI := (towerMap A t p a b hab).toRingHom.toAlgebra
    RelStage A t p a b →ₐ[TowerStage A t p a] TowerStage A t p b :=
  letI := (towerMap A t p a b hab).toRingHom.toAlgebra
  Ideal.Quotient.liftₐ _ (aeval fun i ↦ Ideal.Quotient.mk (towerRel A t p b) (X i))
    (relIdeal_apply_eq_zero (stageX A t p a) (p ^ (b - a)) _ fun i ↦ by
      rw [aeval_X, RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        towerMap_stageX, map_pow])

/-- `A_b` から相対的な段へ（`A` 代数の準同型）：`X_i ↦ Y_i`。 -/
noncomputable def relStageFrom : TowerStage A t p b →ₐ[A] RelStage A t p a b :=
  Ideal.Quotient.liftₐ _
    (aeval fun i ↦ Ideal.Quotient.mk _ (X i : MvPolynomial (Fin h) (TowerStage A t p a)))
    (relIdeal_apply_eq_zero t (p ^ b) _ fun i ↦ by
      have hb : p ^ b = p ^ (b - a) * p ^ a := by rw [← pow_add, Nat.sub_add_cancel hab]
      rw [aeval_X, hb, pow_mul, mk_Y_pow, ← map_pow, mk_X_pow,
        ← IsScalarTower.algebraMap_apply A (TowerStage A t p a) (RelStage A t p a b)])

omit [Fact p.Prime] in
lemma relStageTo_mk_X (i : Fin h) :
    relStageTo A t p a b hab (Ideal.Quotient.mk _ (X i)) =
      Ideal.Quotient.mk (towerRel A t p b) (X i) := by
  let _ := (towerMap A t p a b hab).toRingHom.toAlgebra
  exact aeval_X (fun i ↦ Ideal.Quotient.mk (towerRel A t p b) (X i)) i

omit [Fact p.Prime] in
lemma relStageFrom_mk_X (i : Fin h) :
    relStageFrom A t p a b hab (Ideal.Quotient.mk _ (X i)) =
      Ideal.Quotient.mk _ (X i : MvPolynomial (Fin h) (TowerStage A t p a)) := by
  exact aeval_X (R := A)
    (fun i ↦ (Ideal.Quotient.mk _ (X i) : RelStage A t p a b)) i

omit [Fact p.Prime] in
/-- `relStageFrom ∘ towerMap = algebraMap A_a (RelStage)`。 -/
lemma relStageFrom_towerMap (x : TowerStage A t p a) :
    relStageFrom A t p a b hab (towerMap A t p a b hab x) =
      algebraMap _ (RelStage A t p a b) x := by
  have : (relStageFrom A t p a b hab).comp (towerMap A t p a b hab) =
      IsScalarTower.toAlgHom A (TowerStage A t p a) (RelStage A t p a b) := by
    refine Ideal.Quotient.algHom_ext A ?_
    refine MvPolynomial.algHom_ext fun i ↦ ?_
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, IsScalarTower.coe_toAlgHom']
    rw [towerMap_stageX, map_pow, map_pow, relStageFrom_mk_X, mk_Y_pow]
  exact AlgHom.congr_fun this x

omit [Fact p.Prime] in
lemma relStageTo_comp_relStageFrom :
    letI := (towerMap A t p a b hab).toRingHom.toAlgebra
    (relStageTo A t p a b hab).toRingHom.comp (relStageFrom A t p a b hab).toRingHom =
      RingHom.id _ := by
  let _ := (towerMap A t p a b hab).toRingHom.toAlgebra
  refine Ideal.Quotient.ringHom_ext ?_
  refine MvPolynomial.ringHom_ext (fun x ↦ ?_) (fun i ↦ ?_)
  · simp only [RingHom.comp_apply, RingHom.id_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
    rw [← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap, AlgHom.commutes,
      IsScalarTower.algebraMap_apply A (TowerStage A t p a) (RelStage A t p a b),
      (relStageTo A t p a b hab).commutes, RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, AlgHom.commutes]
  · simp only [RingHom.comp_apply, RingHom.id_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
    rw [relStageFrom_mk_X, relStageTo_mk_X]

omit [Fact p.Prime] in
lemma relStageFrom_comp_relStageTo :
    letI := (towerMap A t p a b hab).toRingHom.toAlgebra
    (relStageFrom A t p a b hab).toRingHom.comp (relStageTo A t p a b hab).toRingHom =
      RingHom.id _ := by
  let _ := (towerMap A t p a b hab).toRingHom.toAlgebra
  refine Ideal.Quotient.ringHom_ext ?_
  refine MvPolynomial.ringHom_ext (fun s ↦ ?_) (fun i ↦ ?_)
  · simp only [RingHom.comp_apply, RingHom.id_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
    rw [← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap,
      (relStageTo A t p a b hab).commutes, RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, relStageFrom_towerMap]
  · simp only [RingHom.comp_apply, RingHom.id_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
    rw [relStageTo_mk_X, relStageFrom_mk_X]

/-- 相対的な段と `A_b` の環同型。 -/
noncomputable def relStageRingEquiv : RelStage A t p a b ≃+* TowerStage A t p b :=
  letI := (towerMap A t p a b hab).toRingHom.toAlgebra
  RingEquiv.ofRingHom (relStageTo A t p a b hab).toRingHom (relStageFrom A t p a b hab).toRingHom
    (relStageTo_comp_relStageFrom A t p a b hab) (relStageFrom_comp_relStageTo A t p a b hab)

/-- 相対的な段と `A_b` の同型（`A_a` 代数として）。 -/
noncomputable def relStageEquiv :
    letI := (towerMap A t p a b hab).toRingHom.toAlgebra
    RelStage A t p a b ≃ₐ[TowerStage A t p a] TowerStage A t p b :=
  letI := (towerMap A t p a b hab).toRingHom.toAlgebra
  AlgEquiv.ofRingEquiv (f := relStageRingEquiv A t p a b hab) fun x ↦
    (relStageTo A t p a b hab).commutes x

/-- `A_b` の `A_a` 上の単項式基底 `X^e`（`0 ≤ e_i < p^{b−a}`）。 -/
noncomputable def towerMapBasis :
    letI := (towerMap A t p a b hab).toRingHom.toAlgebra
    Module.Basis (Fin h → Fin (p ^ (b - a))) (TowerStage A t p a) (TowerStage A t p b) :=
  letI := (towerMap A t p a b hab).toRingHom.toAlgebra
  (relBasis (TowerStage A t p a) (stageX A t p a) (p ^ (b - a)) (pow_pos_of_prime p (b - a))).map
    (relStageEquiv A t p a b hab).toLinearEquiv

end relative

/-- `A_a → A_b` は有限自由でランク `p^{(b−a)h}`。 -/
theorem towerMap_free_finrank [Nontrivial A] (a b : ℕ) (hab : a ≤ b) :
    letI := (towerMap A t p a b hab).toRingHom.toAlgebra
    Module.Free (TowerStage A t p a) (TowerStage A t p b) ∧
      Module.Finite (TowerStage A t p a) (TowerStage A t p b) ∧
      Module.finrank (TowerStage A t p a) (TowerStage A t p b) = stageRank h p (b - a) := by
  let _ := (towerMap A t p a b hab).toRingHom.toAlgebra
  have hq := pow_pos_of_prime p (b - a)
  have hnt : Nontrivial (TowerStage A t p a) :=
    nontrivial_of_ne _ _ ((towerStageBasis A t p a).ne_zero fun _ ↦ ⟨0, pow_pos_of_prime p a⟩)
  have hfree := free_quotient_relIdeal (TowerStage A t p a) (stageX A t p a) _ hq
  have hfin := finite_quotient_relIdeal (TowerStage A t p a) (stageX A t p a) _ hq
  refine ⟨Module.Free.of_equiv (relStageEquiv A t p a b hab).toLinearEquiv,
    Module.Finite.equiv (relStageEquiv A t p a b hab).toLinearEquiv, ?_⟩
  rw [← (relStageEquiv A t p a b hab).toLinearEquiv.finrank_eq, stageRank, pow_mul]
  exact finrank_quotient_relIdeal (TowerStage A t p a) (stageX A t p a) _ hq

/-! ## 局所環と剰余体

`A_n → k`、`X_i ↦ 0`、`a ↦ ā` の核 `M` は極大イデアルで、`m_A A_n` と全ての `X_i` で生成される。
任意の極大イデアル `M'` は整拡大なので `m_A` の上にあり（`Ideal.isMaximal_comap_of_isIntegral_of_isMaximal`）、
`X_i^{p^n} = t_i ∈ m_A A_n ⊆ M'` と素性から `X_i ∈ M'`。よって `M ⊆ M'`、極大性から `M = M'`。 -/

section local_ring

variable [IsLocalRing A] (ht : ∀ i, t i ∈ maximalIdeal A)

include ht in
/-- 関係式 `X_i^{p^n} − t_i` は `X_i ↦ 0`、`a ↦ ā` で `0` になる。 -/
lemma towerRel_le_ker_eval₂Hom_residue (n : ℕ) :
    towerRel A t p n ≤ RingHom.ker (eval₂Hom (residue A) (0 : Fin h → ResidueField A)) := by
  rw [towerRel, relIdeal, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_pow, eval₂Hom_X', eval₂Hom_C, Pi.zero_apply,
    zero_pow (pow_pos_of_prime p n).ne', (residue_eq_zero_iff _).mpr (ht i), sub_zero]

/-- `A_n → k`：`X_i ↦ 0`、`a ↦ ā`。 -/
noncomputable def stageResidue (n : ℕ) : TowerStage A t p n →+* ResidueField A :=
  Ideal.Quotient.lift (towerRel A t p n) (eval₂Hom (residue A) 0)
    fun _ hx ↦ RingHom.mem_ker.mp (towerRel_le_ker_eval₂Hom_residue A t p ht n hx)

lemma stageResidue_mk (n : ℕ) (f : MvPolynomial (Fin h) A) :
    stageResidue A t p ht n (Ideal.Quotient.mk _ f) = residue A (constantCoeff f) :=
  eval₂Hom_zero_apply (residue A) f

lemma stageResidue_algebraMap (n : ℕ) (x : A) :
    stageResidue A t p ht n (algebraMap A (TowerStage A t p n) x) = residue A x := by
  rw [← Ideal.Quotient.mk_algebraMap, stageResidue_mk, MvPolynomial.algebraMap_eq, constantCoeff_C]

lemma stageResidue_surjective (n : ℕ) : Function.Surjective (stageResidue A t p ht n) := by
  intro y
  obtain ⟨x, rfl⟩ := residue_surjective y
  exact ⟨algebraMap A _ x, stageResidue_algebraMap A t p ht n x⟩

/-- `ker (A_n → k)` は極大イデアル。 -/
theorem ker_stageResidue_isMaximal (n : ℕ) :
    (RingHom.ker (stageResidue A t p ht n)).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (stageResidue_surjective A t p ht n)

omit [Fact p.Prime] [IsLocalRing A] in
/-- `f` の像から定数項を引いたものは、全ての `X_i` を含むイデアルに入る。 -/
lemma mk_sub_constantCoeff_mem (n : ℕ) (M : Ideal (TowerStage A t p n))
    (hX : ∀ i, Ideal.Quotient.mk (towerRel A t p n) (X i) ∈ M) (f : MvPolynomial (Fin h) A) :
    Ideal.Quotient.mk (towerRel A t p n) f -
      algebraMap A (TowerStage A t p n) (constantCoeff f) ∈ M := by
  induction f using MvPolynomial.induction_on with
  | C x =>
    rw [constantCoeff_C, ← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq, sub_self]
    exact M.zero_mem
  | add f g hf hg =>
    rw [map_add, map_add, map_add, add_sub_add_comm]
    exact M.add_mem hf hg
  | mul_X f i hf =>
    simp only [map_mul, constantCoeff_X, mul_zero, map_zero, sub_zero]
    exact M.mul_mem_left _ (hX i)

/-- `ker (A_n → k)` は `m_A A_n` と全ての `X_i` を含むイデアルに含まれる。 -/
lemma ker_stageResidue_le (n : ℕ) (M : Ideal (TowerStage A t p n))
    (hm : (maximalIdeal A).map (algebraMap A (TowerStage A t p n)) ≤ M)
    (hX : ∀ i, Ideal.Quotient.mk (towerRel A t p n) (X i) ∈ M) :
    RingHom.ker (stageResidue A t p ht n) ≤ M := by
  intro x hx
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [RingHom.mem_ker, stageResidue_mk, residue_eq_zero_iff] at hx
  rw [← sub_add_cancel (Ideal.Quotient.mk _ f)
    (algebraMap A (TowerStage A t p n) (constantCoeff f))]
  exact M.add_mem (mk_sub_constantCoeff_mem A t p n M hX f) (hm (Ideal.mem_map_of_mem _ hx))

include ht in
/-- 極大イデアルは `m_A A_n` と全ての `X_i` を含む（整拡大）。 -/
lemma le_of_isMaximal_towerStage (n : ℕ) (M : Ideal (TowerStage A t p n)) [M.IsMaximal] :
    (maximalIdeal A).map (algebraMap A (TowerStage A t p n)) ≤ M ∧
      ∀ i, Ideal.Quotient.mk (towerRel A t p n) (X i) ∈ M := by
  have := isIntegral_towerStage A t p n
  have hcomap : (M.comap (algebraMap A (TowerStage A t p n))).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _ (fun x ↦ Algebra.IsIntegral.isIntegral x) M
  have hm : (maximalIdeal A).map (algebraMap A (TowerStage A t p n)) ≤ M := by
    rw [Ideal.map_le_iff_le_comap, ← IsLocalRing.eq_maximalIdeal hcomap]
  refine ⟨hm, fun i ↦ ?_⟩
  refine (Ideal.IsMaximal.isPrime ‹_›).mem_of_pow_mem (p ^ n) ?_
  rw [mk_X_pow]
  exact hm (Ideal.mem_map_of_mem _ (ht i))

include ht in
/-- 各段は局所環。 -/
theorem isLocalRing_towerStage (n : ℕ) : IsLocalRing (TowerStage A t p n) := by
  refine IsLocalRing.of_unique_max_ideal ⟨RingHom.ker (stageResidue A t p ht n),
    ker_stageResidue_isMaximal A t p ht n, fun M hM ↦ ?_⟩
  have := hM
  obtain ⟨hm, hX⟩ := le_of_isMaximal_towerStage A t p ht n M
  exact ((ker_stageResidue_isMaximal A t p ht n).eq_of_le hM.ne_top
    (ker_stageResidue_le A t p ht n M hm hX)).symm

include ht in
/-- 各段の極大イデアルは `ker (A_n → k)`。 -/
theorem maximalIdeal_towerStage (n : ℕ) :
    haveI := isLocalRing_towerStage A t p ht n
    maximalIdeal (TowerStage A t p n) = RingHom.ker (stageResidue A t p ht n) :=
  haveI := isLocalRing_towerStage A t p ht n
  (IsLocalRing.eq_maximalIdeal (ker_stageResidue_isMaximal A t p ht n)).symm

include ht in
/-- 各段の剰余体は `k`：`A → A_n → A_n/m` は全射。 -/
theorem residue_surjective_towerStage (n : ℕ) :
    haveI := isLocalRing_towerStage A t p ht n
    Function.Surjective
      ((residue (TowerStage A t p n)).comp (algebraMap A (TowerStage A t p n))) := by
  have := isLocalRing_towerStage A t p ht n
  intro y
  obtain ⟨x, rfl⟩ := residue_surjective y
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨constantCoeff f, ?_⟩
  rw [RingHom.comp_apply]
  symm
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, maximalIdeal_towerStage A t p ht n,
    RingHom.mem_ker, map_sub, stageResidue_mk, stageResidue_algebraMap, sub_self]

include ht in
/-- 各段は完備。完備ネーター局所環の有限な局所環拡大の完備性を適用する。 -/
theorem isAdicComplete_towerStage [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A] (n : ℕ) :
    haveI := isLocalRing_towerStage A t p ht n
    IsAdicComplete (maximalIdeal (TowerStage A t p n)) (TowerStage A t p n) := by
  let := isLocalRing_towerStage A t p ht n
  let := towerStage_finite A t p n
  exact isAdicComplete_finite_local_algebra (R := A) (TowerStage A t p n)

include ht in
/-- パラメータ系が基底の極大イデアルを生成すれば、各段の根がその段の極大イデアルを生成する。 -/
theorem span_stageX_eq_maximalIdeal
    (ht' : Ideal.span (Set.range t) = maximalIdeal A) (n : ℕ) :
    haveI := isLocalRing_towerStage A t p ht n
    Ideal.span (Set.range (stageX A t p n)) = maximalIdeal (TowerStage A t p n) := by
  let := isLocalRing_towerStage A t p ht n
  rw [maximalIdeal_towerStage A t p ht n]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp [stageX, RingHom.mem_ker, stageResidue_mk]
  · apply ker_stageResidue_le A t p ht n
    · rw [← ht', Ideal.map_span, ← Set.range_comp, Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      rw [Function.comp_apply, ← mk_X_pow A t p n i]
      exact Ideal.pow_mem_of_mem _ (Ideal.subset_span (Set.mem_range_self i)) _
        (pow_pos_of_prime p n)
    · intro i
      exact Ideal.subset_span (Set.mem_range_self i)

end local_ring

/-! ## `Λ` の平坦性

`Λ = lim→ A_m` は `A_n` 上、有限自由加群 `A_m`（`m ≥ n`）の有向極限なので平坦。等式的判定法
（`Module.Flat.of_forall_exists_factorization`）で示す：`A_n^l → Λ` が `f` を消すなら、生成元の像が
入る段 `m` をとり、関係式が消える段 `m' ≥ m` をとれば、`A_n^l → A_{m'} ≅ A_n^k → Λ` と分解する。 -/

section flat

variable (n m : ℕ) (hnm : n ≤ m)

/-- `towerOf m` は `A_n` 代数の準同型（`A_m` を `towerMap n m` で `A_n` 代数とみる）。 -/
noncomputable def towerOfₐ :
    letI := (towerMap A t p n m hnm).toRingHom.toAlgebra
    TowerStage A t p m →ₐ[TowerStage A t p n] Tower A t p :=
  letI := (towerMap A t p n m hnm).toRingHom.toAlgebra
  { towerOf A t p m with commutes' := fun s ↦ towerOf_towerMap A t p n m hnm s }

omit [Fact p.Prime] in
lemma towerOfₐ_apply (y : TowerStage A t p m) : towerOfₐ A t p n m hnm y = towerOf A t p m y := rfl

/-- `towerMap m m'` は `A_n` 代数の準同型。 -/
noncomputable def towerMapₐ (m' : ℕ) (hmm' : m ≤ m') :
    letI := (towerMap A t p n m hnm).toRingHom.toAlgebra
    letI := (towerMap A t p n m' (hnm.trans hmm')).toRingHom.toAlgebra
    TowerStage A t p m →ₐ[TowerStage A t p n] TowerStage A t p m' :=
  letI := (towerMap A t p n m hnm).toRingHom.toAlgebra
  letI := (towerMap A t p n m' (hnm.trans hmm')).toRingHom.toAlgebra
  { towerMap A t p m m' hmm' with
    commutes' := fun s ↦ towerMap_towerMap A t p n m m' hnm hmm' s }

omit [Fact p.Prime] in
lemma towerMapₐ_apply (m' : ℕ) (hmm' : m ≤ m') (y : TowerStage A t p m) :
    towerMapₐ A t p n m hnm m' hmm' y = towerMap A t p m m' hmm' y := rfl

end flat

/-- `Λ` は各段の上で平坦（有限自由加群の有向極限）。Lemma 5.4 で `Tor` を段に降ろすのに使う。 -/
theorem flat_tower (n : ℕ) : Module.Flat (TowerStage A t p n) (Tower A t p) := by
  classical
  refine Module.Flat.of_forall_exists_factorization fun {l} {f} {x} hx ↦ ?_
  -- 生成元の像が入る段 `m ≥ n`
  choose ms ys hys using fun i : Fin l ↦ exists_towerOf A t p (x (Finsupp.single i 1))
  set m : ℕ := n ⊔ Finset.univ.sup ms with hm
  have hnm : n ≤ m := le_sup_left
  have hms : ∀ i, ms i ≤ m := fun i ↦ le_sup_of_le_right (Finset.le_sup (Finset.mem_univ i))
  let _ := (towerMap A t p n m hnm).toRingHom.toAlgebra
  let y' : Fin l → TowerStage A t p m := fun i ↦ towerMap A t p (ms i) m (hms i) (ys i)
  have hy' : ∀ i, towerOf A t p m (y' i) = x (Finsupp.single i 1) := fun i ↦ by
    simp only [y', towerOf_towerMap, hys]
  let x' : (Fin l →₀ TowerStage A t p n) →ₗ[TowerStage A t p n] TowerStage A t p m :=
    Finsupp.linearCombination _ y'
  have hx' : (towerOfₐ A t p n m hnm).toLinearMap ∘ₗ x' = x := by
    refine Finsupp.lhom_ext' fun i ↦ LinearMap.ext_ring ?_
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, AlgHom.toLinearMap_apply,
      towerOfₐ_apply, x', Finsupp.linearCombination_single, one_smul, hy']
  -- 関係式が消える段 `m' ≥ m`
  have h0 : towerOf A t p m (x' f) = 0 := by
    rw [← hx, ← hx']
    rfl
  obtain ⟨m', hmm', hm'⟩ := Ring.DirectLimit.of.zero_exact (G := fun n ↦ TowerStage A t p n)
    (f' := towerMapRingHom A t p) h0
  rw [towerMapRingHom_apply] at hm'
  let _ := (towerMap A t p n m' (hnm.trans hmm')).toRingHom.toAlgebra
  -- `A_{m'}` の `A_n` 上の有限基底を `Fin k` で添字づける
  let e : TowerStage A t p m' ≃ₗ[TowerStage A t p n]
      (Fin (Fintype.card (Fin h → Fin (p ^ (m' - n)))) →₀ TowerStage A t p n) :=
    (towerMapBasis A t p n m' (hnm.trans hmm')).repr.trans
      (Finsupp.domLCongr (Fintype.equivFin _))
  refine ⟨_, e.toLinearMap ∘ₗ (towerMapₐ A t p n m hnm m' hmm').toLinearMap ∘ₗ x',
    (towerOfₐ A t p n m' (hnm.trans hmm')).toLinearMap ∘ₗ e.symm.toLinearMap, ?_, ?_⟩
  · rw [← hx']
    refine LinearMap.ext fun v ↦ ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      AlgHom.toLinearMap_apply, towerOfₐ_apply, towerMapₐ_apply, towerOf_towerMap]
  · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, AlgHom.toLinearMap_apply, towerMapₐ_apply]
    rw [show towerMap A t p m m' hmm' (x' f) = 0 from hm', map_zero]

/-- 各段は正則局所環。単射な整拡大による次元保存で `dim A_n = h` を得る。
極大イデアルを `h` 個の根が生成するので、Mathlib の生成元数による正則性判定を適用する。 -/
theorem isRegularLocalRing_towerStage [IsRegularLocalRing A]
    (ht' : Ideal.span (Set.range t) = maximalIdeal A) (hdim : ringKrullDim A = h) (n : ℕ) :
    IsRegularLocalRing (TowerStage A t p n) := by
  have ht : ∀ i, t i ∈ maximalIdeal A := fun i ↦ ht' ▸ Ideal.subset_span (Set.mem_range_self i)
  let := isLocalRing_towerStage A t p ht n
  let := towerStage_finite A t p n
  let := towerStage_free A t p n
  let := isIntegral_towerStage A t p n
  let : IsNoetherianRing (TowerStage A t p n) := IsNoetherianRing.of_finite A _
  have hdimn : ringKrullDim (TowerStage A t p n) = h :=
    (ringKrullDim_eq_of_integral_of_injective A _
      (FaithfulSMul.algebraMap_injective A _)).trans hdim
  let x : Fin h → TowerStage A t p n := fun i ↦ Ideal.Quotient.mk _ (X i)
  have hspan : Ideal.span (Set.range x) = maximalIdeal (TowerStage A t p n) :=
    span_stageX_eq_maximalIdeal A t p ht ht' n
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [← hspan, hdimn]
  have hgen : (Ideal.span (Set.range x)).spanFinrank ≤ h :=
    (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range x)).trans
      (by simpa only [Set.image_univ, Set.ncard_univ, Nat.card_fin] using
        Set.ncard_image_le (s := Set.univ) (f := x))
  exact_mod_cast hgen

end Section2

end SerrePositivity
