module

public import SerrePositivity.CommutativeAlgebra.PBasisLifting
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.Algebra.CharP.Quotient
public import SerrePositivity.FieldTheory.PIndependentSet
public import Mathlib.RingTheory.AdicCompletion.RingHom
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! # 完備な核に沿う p 基底の持ち上げと係数体

概要：標数 `p` の環の全射 `f : A → k`（`k` は体）で、`A` が核 `I` について完備とする。`k` の p 基底 `b` と
持ち上げ `β` を指定すると、`f` の切断 `k → A` で `b_i ↦ β_i` となるものが一意に存在する
（`IsPBasis.liftOfCompleteKernel`）。系として、同標数 `p` の完備局所環は任意の剰余体について係数体を持ち、
剰余体の p 基底の持ち上げを指定した係数写像は一意。
方針：各冪商 `A/I^{n+1} → k` の核は `(n+1)` 乗で零なので、`p^{n+1}` 乗で消える。冪零核の場合
（`PBasisLifting`）の切断を各段で取り、一意性から段の間で両立することを確かめ、Mathlib の完備性の普遍性
（`StrictMono.liftRingHom`）で逆極限を取る。
規約：完全体性・有限 p 次数・Noether 性は仮定しない。
使われ方：同標数の有限正規化（`EqualCharacteristicNormalization`）と Cohen–Gabber の係数切断の取り替え。
Matsumura Theorem 28.3 の同標数の場合で、Mathlib への提出候補（mathlib-upstream の G2）。
-/

@[expose] public noncomputable section
namespace SerrePositivity

section KernelPowerQuotient

variable {A B : Type*} [CommRing A] [CommRing B]

/-- 核の正の冪による商から、元の写像の終域への写像。 -/
def kernelPowerQuotientMap (f : A →+* B) (n : ℕ) : A ⧸ (RingHom.ker f) ^ (n + 1) →+* B :=
  Ideal.Quotient.lift _ f ((RingHom.ker f).pow_le_self (Nat.succ_ne_zero n))

@[simp] theorem kernelPowerQuotientMap_mk (f : A →+* B) (n : ℕ) (x : A) :
    kernelPowerQuotientMap f n (Ideal.Quotient.mk ((RingHom.ker f) ^ (n + 1)) x) = f x := rfl

theorem kernelPowerQuotientMap_surjective (f : A →+* B) (hf : Function.Surjective f) (n : ℕ) :
    Function.Surjective (kernelPowerQuotientMap f n) :=
  Ideal.Quotient.lift_surjective_of_surjective _ _ hf

/-- 商の写像の核の `n + 1` 乗は零。 -/
theorem kernelPowerQuotientMap_ker_pow_eq_bot (f : A →+* B) (n : ℕ) :
    RingHom.ker (kernelPowerQuotientMap f n) ^ (n + 1) = ⊥ := by
  rw [kernelPowerQuotientMap, Ideal.ker_quotient_lift, ← Ideal.map_pow,
    Ideal.map_quotient_self]

/-- 商の写像の核はイデアルとして冪零。各元の冪零性だけではない。 -/
theorem kernelPowerQuotientMap_nilpotent_kernel (f : A →+* B) (n : ℕ) :
    IsNilpotent (RingHom.ker (kernelPowerQuotientMap f n)) :=
  ⟨n + 1, kernelPowerQuotientMap_ker_pow_eq_bot f n⟩

/-- 源と終域の標数が一致すれば、正の冪商にも同じ標数が入る。 -/
theorem kernelPowerQuotient_charP (f : A →+* B) (p n : ℕ) [CharP A p] [CharP B p] :
    CharP (A ⧸ (RingHom.ker f) ^ (n + 1)) p :=
  CharP.quotient' p _ (fun a ha ↦ by
    have h : f (a : A) = 0 := (RingHom.ker f).pow_le_self (Nat.succ_ne_zero n) ha
    rw [map_natCast] at h
    exact (CharP.cast_eq_zero_iff A p a).mpr ((CharP.cast_eq_zero_iff B p a).mp h))

theorem kernelPowerQuotientMap_comp_factorPowSucc (f : A →+* B) (n : ℕ) :
    (kernelPowerQuotientMap f n).comp (Ideal.Quotient.factorPowSucc (RingHom.ker f) (n + 1)) =
      kernelPowerQuotientMap f (n + 1) := by
  ext x
  simp

end KernelPowerQuotient
open IsLocalRing IsAdicComplete

variable {k A ι : Type*} [Field k] [CommRing A] {p : ℕ} [Fact p.Prime]
  [CharP k p] [CharP A p] {b : ι → k}

section Complete

variable (hb : IsPBasis k p b) (f : A →+* k) (hf : Function.Surjective f)
  (β : ι → A) (hβ : ∀ i, f (β i) = b i)

/-- 第 `n` 段の切断 `k → A/I^{n+1}`。 -/
def IsPBasis.liftOfCompleteKernelStage (n : ℕ) : k →+* A ⧸ (RingHom.ker f) ^ (n + 1) :=
  letI := kernelPowerQuotient_charP f p n
  hb.liftOfFrobeniusKernel (kernelPowerQuotientMap f n)
    (kernelPowerQuotientMap_surjective f hf n)
    (n + 1) (pow_exp_eq_zero_of_pow_eq_bot p _ (kernelPowerQuotientMap_ker_pow_eq_bot f n))
    (fun i ↦ Ideal.Quotient.mk _ (β i)) hβ

theorem IsPBasis.comp_liftOfCompleteKernelStage (n : ℕ) :
    (kernelPowerQuotientMap f n).comp (hb.liftOfCompleteKernelStage f hf β hβ n) =
      RingHom.id k :=
  let := kernelPowerQuotient_charP f p n
  hb.comp_liftOfFrobeniusKernel _ _ _ _ _ _

theorem IsPBasis.liftOfCompleteKernelStage_apply (n : ℕ) (i : ι) :
    hb.liftOfCompleteKernelStage f hf β hβ n (b i) = Ideal.Quotient.mk _ (β i) :=
  let := kernelPowerQuotient_charP f p n
  hb.liftOfFrobeniusKernel_apply _ _ _ _ _ _ i

/-- 隣り合う段の切断は両立する。 -/
theorem IsPBasis.liftOfCompleteKernelStage_compat (n : ℕ) :
    (Ideal.Quotient.factorPowSucc (RingHom.ker f) (n + 1)).comp
      (hb.liftOfCompleteKernelStage f hf β hβ (n + 1)) =
        hb.liftOfCompleteKernelStage f hf β hβ n := by
  let := kernelPowerQuotient_charP f p n
  apply hb.ringHom_lift_unique_of_frobenius_kernel (kernelPowerQuotientMap f n) (n + 1)
    (pow_exp_eq_zero_of_pow_eq_bot p _ (kernelPowerQuotientMap_ker_pow_eq_bot f n))
  · rw [← RingHom.comp_assoc, kernelPowerQuotientMap_comp_factorPowSucc,
      hb.comp_liftOfCompleteKernelStage, hb.comp_liftOfCompleteKernelStage]
  · intro i
    change Ideal.Quotient.factorPowSucc _ (n + 1)
      (hb.liftOfCompleteKernelStage f hf β hβ (n + 1) (b i)) = _
    rw [hb.liftOfCompleteKernelStage_apply, hb.liftOfCompleteKernelStage_apply]
    simp

variable [IsAdicComplete (RingHom.ker f) A]

/-- 核について完備な全射に沿う切断で、`b_i` を `β_i` へ送るもの。冪商の切断の逆極限。 -/
def IsPBasis.liftOfCompleteKernel : k →+* A :=
  Order.succ_strictMono.liftRingHom (RingHom.ker f) (hb.liftOfCompleteKernelStage f hf β hβ)
    fun {n} ↦ hb.liftOfCompleteKernelStage_compat f hf β hβ n

theorem IsPBasis.mk_liftOfCompleteKernel (n : ℕ) (x : k) :
    Ideal.Quotient.mk ((RingHom.ker f) ^ (n + 1)) (hb.liftOfCompleteKernel f hf β hβ x) =
      hb.liftOfCompleteKernelStage f hf β hβ n x :=
  Order.succ_strictMono.mk_liftRingHom (RingHom.ker f) _ _ (n := n) x

@[simp] theorem IsPBasis.comp_liftOfCompleteKernel :
    f.comp (hb.liftOfCompleteKernel f hf β hβ) = RingHom.id k := by
  ext x
  have h := RingHom.congr_fun (hb.comp_liftOfCompleteKernelStage f hf β hβ 0) x
  change kernelPowerQuotientMap f 0 (hb.liftOfCompleteKernelStage f hf β hβ 0 x) = x at h
  rw [← hb.mk_liftOfCompleteKernel f hf β hβ 0 x] at h
  exact h

@[simp] theorem IsPBasis.liftOfCompleteKernel_apply (i : ι) :
    hb.liftOfCompleteKernel f hf β hβ (b i) = β i := by
  apply (IsHausdorff.eq_iff_smodEq (I := RingHom.ker f)).mpr
  intro n
  cases n with
  | zero => simp
  | succ n =>
    have h := hb.mk_liftOfCompleteKernel f hf β hβ n (b i)
    rw [hb.liftOfCompleteKernelStage_apply] at h
    simpa only [smul_eq_mul, Ideal.mul_top] using
      (SModEq.sub_mem.mpr (Ideal.Quotient.eq.mp h) :
        hb.liftOfCompleteKernel f hf β hβ (b i) ≡ β i [SMOD (RingHom.ker f) ^ (n + 1)])

include hb hf hβ in
/-- 核について完備な全射に沿う、指定 p 基底の像を持つ切断は一意に存在する。 -/
theorem IsPBasis.existsUnique_ringHom_lift_of_complete_kernel :
    ∃! g : k →+* A, f.comp g = RingHom.id k ∧ ∀ i, g (b i) = β i :=
  ⟨hb.liftOfCompleteKernel f hf β hβ,
    ⟨hb.comp_liftOfCompleteKernel f hf β hβ, hb.liftOfCompleteKernel_apply f hf β hβ⟩,
    fun l hl ↦ hb.ringHom_lift_unique_of_hausdorff_kernel f l _
      (hl.1.trans (hb.comp_liftOfCompleteKernel f hf β hβ).symm)
      (fun i ↦ (hl.2 i).trans (hb.liftOfCompleteKernel_apply f hf β hβ i).symm)⟩

end Complete

section CoefficientField

omit [CharP k p] [CharP A p] in
/-- p 基底の存在から、核について完備な全射の切断を構成する。 -/
theorem exists_ringHom_section_of_complete_kernel
    (p : ℕ) [Fact p.Prime] [CharP k p] [CharP A p]
    (f : A →+* k) (hf : Function.Surjective f) [IsAdicComplete (RingHom.ker f) A] :
    ∃ g : k →+* A, f.comp g = RingHom.id k := by
  classical
  obtain ⟨s, hs⟩ := exists_pBasis (K := k) (p := p)
  choose β hβ using (fun i : s ↦ hf (i : k))
  exact ⟨hs.liftOfCompleteKernel f hf β hβ, hs.comp_liftOfCompleteKernel f hf β hβ⟩

variable [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A]

omit [CharP k p] in
/-- 剰余体の p 基底の持ち上げを指定した係数写像は一意に存在する。 -/
theorem IsPBasis.existsUnique_coefficientRingHom {ι : Type*} [CharP (ResidueField A) p]
    {b : ι → ResidueField A} (hb : IsPBasis (ResidueField A) p b)
    (β : ι → A) (hβ : ∀ i, residue A (β i) = b i) :
    ∃! g : ResidueField A →+* A,
      (residue A).comp g = RingHom.id (ResidueField A) ∧ ∀ i, g (b i) = β i := by
  let : IsAdicComplete (RingHom.ker (residue A)) A := by
    rw [ker_residue]
    infer_instance
  exact hb.existsUnique_ringHom_lift_of_complete_kernel (residue A) residue_surjective β hβ

omit [CharP k p] [CharP A p] in
/-- 同標数 `p` の完備局所環は任意の剰余体について係数体を持つ。Noether 性は不要。 -/
theorem exists_coefficientField_ringHom (p : ℕ) [Fact p.Prime] [CharP A p] :
    ∃ g : ResidueField A →+* A,
      Function.Injective g ∧ IsLocalHom g ∧
        (residue A).comp g = RingHom.id (ResidueField A) := by
  let : CharP (ResidueField A) p :=
    (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr (by
      rw [← map_natCast (residue A), CharP.cast_eq_zero, map_zero])
  let : IsAdicComplete (RingHom.ker (residue A)) A := by
    rw [ker_residue]
    infer_instance
  obtain ⟨g, hg⟩ := exists_ringHom_section_of_complete_kernel p
    (residue A) residue_surjective
  exact ⟨g, g.injective, inferInstance, hg⟩

end CoefficientField

end SerrePositivity
