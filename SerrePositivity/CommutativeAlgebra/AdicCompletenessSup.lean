module

public import SerrePositivity.CommutativeAlgebra.AdicCompleteness
public import Mathlib.LinearAlgebra.Quotient.Basic

/-! # 二つのイデアルの和に沿う完備性

I進完備性と、各I冪商のJ進完備性から(I+J)進完備性を構成する。
商でのJ進極限の両立を確認し、I進極限へ戻す。
-/

public section
namespace SerrePositivity
variable {R : Type*} [CommRing R]

/-- I商でのJ冪合同は、元の環でのI+J冪合同に等しい。 -/
theorem smodEq_quotient_iff_sup (I J : Ideal R) (n : ℕ) (x y : R) :
    I.mkQ x ≡ I.mkQ y [SMOD (J ^ n • (⊤ : Submodule R (R ⧸ I)))] ↔
      x ≡ y [SMOD (I ⊔ J ^ n)] := by
  have he : (J ^ n • (⊤ : Submodule R (R ⧸ I))).comap I.mkQ = I ⊔ J ^ n := by
    have hm : Submodule.map I.mkQ (J ^ n : Submodule R R) =
        J ^ n • (⊤ : Submodule R (R ⧸ I)) := by
      have ht : (J ^ n : Submodule R R) = J ^ n • (⊤ : Submodule R R) := by
        simp only [smul_eq_mul, Ideal.mul_top]
      nth_rw 1 [ht]
      rw [Submodule.map_smul'', Submodule.map_top, I.range_mkQ]
    rw [← hm, Submodule.comap_map_mkQ]
  simp only [SModEq.sub_mem, ← map_sub, ← Submodule.mem_comap, he]

/-- I進完備性と全I冪商のJ進完備性から、I+J進完備性を導く。 -/
theorem isAdicComplete_sup_of_complete_quotients (I J : Ideal R)
    [IsAdicComplete I R] [∀ n : ℕ, IsAdicComplete J (R ⧸ I ^ n)] :
    IsAdicComplete (I ⊔ J) R := by
  classical
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    apply IsHausdorff.haus (inferInstance : IsHausdorff I R) x
    intro n
    have hzero : (I ^ n).mkQ x = 0 := by
      apply (IsHausdorff.eq_iff_smodEq (I := J)).mpr
      intro k
      apply (smodEq_quotient_iff_sup (I ^ n) J k x 0).mpr
      have hh := hx (n + k)
      simp only [smul_eq_mul, Ideal.mul_top] at hh
      exact hh.mono Ideal.sup_pow_add_le_pow_sup_pow
    simpa only [smul_eq_mul, Ideal.mul_top] using
      SModEq.sub_mem.mpr ((Submodule.Quotient.eq _).mp hzero)
  · intro f hf
    have hlim (n : ℕ) : ∃ L : R ⧸ I ^ n, ∀ k : ℕ,
        (I ^ n).mkQ (f (n + k)) ≡ L [SMOD (J ^ k • (⊤ : Submodule R (R ⧸ I ^ n)))] := by
      apply IsPrecomplete.prec' (I := J)
      intro a b hab
      apply (smodEq_quotient_iff_sup (I ^ n) J a _ _).mpr
      have hh := hf (Nat.add_le_add_left hab n)
      simp only [smul_eq_mul, Ideal.mul_top] at hh
      exact hh.mono Ideal.sup_pow_add_le_pow_sup_pow
    choose L hL using hlim
    choose r hr using (fun n ↦ (I ^ n).mkQ_surjective (L n))
    have ha (n k : ℕ) : f (n + k) ≡ r n [SMOD (I ^ n ⊔ J ^ k)] := by
      apply (smodEq_quotient_iff_sup (I ^ n) J k _ _).mp
      rw [hr]
      exact hL n k
    have hc : ∀ {n m : ℕ}, n ≤ m → r n ≡ r m [SMOD (I ^ n • ⊤ : Ideal R)] := by
      intro n m hnm
      have hq : (I ^ n).mkQ (r n) = (I ^ n).mkQ (r m) := by
        apply (IsHausdorff.eq_iff_smodEq (I := J)).mpr
        intro k
        apply (smodEq_quotient_iff_sup (I ^ n) J k _ _).mpr
        have h1 := (ha n (m + k)).mono
          (sup_le_sup_left (Ideal.pow_le_pow_right (Nat.le_add_left k m)) _)
        have h2 := (ha m (n + k)).mono
          (sup_le_sup (Ideal.pow_le_pow_right hnm)
            (Ideal.pow_le_pow_right (Nat.le_add_left k n)))
        rw [show m + (n + k) = n + (m + k) by omega] at h2
        exact h1.symm.trans h2
      simpa only [smul_eq_mul, Ideal.mul_top] using
        SModEq.sub_mem.mpr ((Submodule.Quotient.eq _).mp hq)
    obtain ⟨a, ha'⟩ := IsPrecomplete.prec' (I := I) r hc
    refine ⟨a, ?_⟩
    intro n
    have h1 := hf (show n ≤ n + n by omega)
    have h2 := (ha n n).mono
      (sup_le (pow_le_pow_left' le_sup_left n) (pow_le_pow_left' le_sup_right n))
    have h3 : r n ≡ a [SMOD ((I ⊔ J) ^ n • ⊤ : Ideal R)] := (ha' n).mono
      (Submodule.smul_mono_left (pow_le_pow_left' (show I ≤ I ⊔ J from le_sup_left) n))
    simp only [smul_eq_mul, Ideal.mul_top] at h1 h3 ⊢
    exact h1.trans (h2.trans h3)

/-- Noether局所環上の有限加群は、極大イデアル以下の完備イデアルに沿って完備。 -/
theorem isAdicComplete_finite_of_ideal_complete
    [IsNoetherianRing R] [IsLocalRing R] (I : Ideal R)
    (hI : I ≤ IsLocalRing.maximalIdeal R) [IsAdicComplete I R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    IsAdicComplete I M := by
  let : IsPrecomplete I M := isPrecomplete_finite I M
  refine { haus' := ?_ }
  intro x hx
  apply IsHausdorff.haus (inferInstance : IsHausdorff (IsLocalRing.maximalIdeal R) M) x
  intro n
  exact (hx n).mono (Submodule.smul_mono_left (pow_le_pow_left' hI n))

/-- Noether局所環でI進・J進の双方に完備なら、和I+Jについても完備。 -/
theorem isAdicComplete_sup_of_noetherian_local
    [IsNoetherianRing R] [IsLocalRing R] (I J : Ideal R)
    (hJ : J ≤ IsLocalRing.maximalIdeal R) [IsAdicComplete I R] [IsAdicComplete J R] :
    IsAdicComplete (I ⊔ J) R := by
  let : ∀ n : ℕ, IsAdicComplete J (R ⧸ I ^ n) := fun n ↦
    isAdicComplete_finite_of_ideal_complete J hJ (R ⧸ I ^ n)
  exact isAdicComplete_sup_of_complete_quotients I J

end SerrePositivity
