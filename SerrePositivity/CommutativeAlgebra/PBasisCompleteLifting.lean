module

public import SerrePositivity.CommutativeAlgebra.PBasisNilpotentLiftExistence
public import SerrePositivity.CommutativeAlgebra.KernelPowerQuotient
public import Mathlib.RingTheory.AdicCompletion.RingHom

/-! # 完備環への指定 p-basis の持ち上げ

正の冪商ごとの一意な切断を両立させ、Mathlib の完備性の普遍性で逆極限を取る。
完全体性、有限 p-rank、Noether 性、局所性は要求しない。
-/

@[expose] public section
namespace SerrePositivity
open IsAdicComplete

variable {k A ι : Type*} [Field k] [CommRing A] {p : ℕ} [Fact p.Prime]
  [CharP k p] [CharP A p] {b : ι → k}

/-- 核について完備な全射に沿う、指定 p-basis の像を持つ一意な切断。 -/
theorem IsPBasis.existsUnique_ringHom_lift_of_complete_kernel (hb : IsPBasis k p b)
    (f : A →+* k) (hf : Function.Surjective f) [IsAdicComplete (RingHom.ker f) A]
    (β : ι → A) (hβ : ∀ i, f (β i) = b i) :
    ∃! g : k →+* A, f.comp g = RingHom.id k ∧ ∀ i, g (b i) = β i := by
  classical
  let I := RingHom.ker f
  let q := kernelPowerQuotientMap f
  have hq (n : ℕ) : ∃! l : k →+* A ⧸ I ^ (n + 1),
      (q n).comp l = RingHom.id k ∧
        ∀ i, l (b i) = Ideal.Quotient.mk (I ^ (n + 1)) (β i) := by
    let : CharP (A ⧸ I ^ (n + 1)) p := kernelPowerQuotient_charP f p n
    apply hb.existsUnique_ringHom_lift_of_nilpotent_kernel (q n)
      (kernelPowerQuotientMap_surjective f hf n)
      (kernelPowerQuotientMap_nilpotent_kernel f n)
    intro i
    exact hβ i
  choose L hL huniq using hq
  have hc (n : ℕ) : (Ideal.Quotient.factorPowSucc I (n + 1)).comp (L (n + 1)) = L n := by
    apply huniq n
    constructor
    · rw [← RingHom.comp_assoc, kernelPowerQuotientMap_comp_factorPowSucc, (hL (n + 1)).1]
    · intro i
      change Ideal.Quotient.factorPowSucc I (n + 1) (L (n + 1) (b i)) = _
      rw [(hL (n + 1)).2]
      simp
  have hc' : ∀ {n}, (Ideal.Quotient.factorPow I
      (Order.succ_strictMono.monotone (Nat.le_succ n))).comp (L (n + 1)) = L n :=
    fun {n} ↦ hc n
  let g := Order.succ_strictMono.liftRingHom I L hc'
  have hg : f.comp g = RingHom.id k := by
    ext x
    have he : Ideal.Quotient.mk (I ^ (0 + 1)) (g x) = L 0 x :=
      Order.succ_strictMono.mk_liftRingHom I L hc' (n := 0) x
    have h := RingHom.congr_fun (hL 0).1 x
    change q 0 (L 0 x) = x at h
    rw [← he] at h
    exact h
  have hgb : ∀ i, g (b i) = β i := by
    intro i
    apply (IsHausdorff.eq_iff_smodEq (I := I)).mpr
    intro n
    cases n with
    | zero => simp
    | succ n =>
      have h : Ideal.Quotient.mk (I ^ (n + 1)) (g (b i)) = L n (b i) :=
        Order.succ_strictMono.mk_liftRingHom I L hc' (n := n) (b i)
      rw [(hL n).2] at h
      simpa only [smul_eq_mul, Ideal.mul_top] using
        (SModEq.sub_mem.mpr (Ideal.Quotient.eq.mp h) : g (b i) ≡ β i [SMOD I ^ (n + 1)])
  refine ⟨g, ⟨hg, hgb⟩, ?_⟩
  intro l hl
  exact hb.ringHom_lift_unique_of_hausdorff_kernel f l g (hl.1.trans hg.symm)
    (fun i ↦ (hl.2 i).trans (hgb i).symm)

end SerrePositivity
