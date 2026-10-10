module

public import SerrePositivity.IntersectionMultiplicity.Additivity
public import SerrePositivity.IntersectionMultiplicity.Equivalence
public import SerrePositivity.CommutativeAlgebra.SupportDimension
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-! # 交点重複度の正値性を素イデアル商へ帰着する

素因子による有限生成加群の帰納法を両変数に適用する。
短完全列の両端は中央以下の次元を持ち、少なくとも一方は同じ次元を持つ。
同じ次元の側は帰納法で正、低次元の側は既存の交点消滅定理で零となる。
このファイルは完備化や剰余体の変更を行わない。
-/

public section

universe u

namespace SerrePositivity

open TensorProduct

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- 第1変数の素イデアル商に対する正値性から、任意の有限生成第1変数へ移す。 -/
theorem chi_pos_of_prime_left
    (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N]
    (hprime : ∀ (P : Ideal R) [P.IsPrime],
      Module.length R ((R ⧸ P) ⊗[R] N) ≠ ⊤ →
      ringKrullDim (R ⧸ P) + Module.supportDim R N = ringKrullDim R →
      0 < chi R (R ⧸ P) N)
    (hfin : Module.length R (M ⊗[R] N) ≠ ⊤)
    (hdim : Module.supportDim R M + Module.supportDim R N = ringKrullDim R) :
    0 < chi R M N := by
  have hforall : ∀ (L : Type u) [AddCommGroup L] [Module R L] [Module.Finite R L],
      Module.length R (L ⊗[R] N) ≠ ⊤ →
      Module.supportDim R L + Module.supportDim R N = ringKrullDim R → 0 < chi R L N := by
    intro L _ _ hL
    induction hL using IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime R with
    | subsingleton L =>
        intro _ hd
        have hb : ringKrullDim R = ⊥ := by
          simpa only [Module.supportDim_eq_bot_of_subsingleton, WithBot.bot_add] using hd.symm
        exact (ringKrullDim_ne_bot (R := R) hb).elim
    | quotient L P e =>
        intro hf hd
        rw [chi_congr e (LinearEquiv.refl R N)]
        apply hprime P.asIdeal
        · rwa [← (TensorProduct.congr e (LinearEquiv.refl R N)).length_eq]
        · rwa [Module.supportDim_eq_of_equiv e, Module.supportDim_quotient_eq_ringKrullDim] at hd
    | exact L₁ L₂ L₃ f g hf hg he ih₁ ih₃ =>
        intro hlength hd
        have h₁ : Module.length R (L₁ ⊗[R] N) ≠ ⊤ := Module.length_ne_top_iff.mpr
          (isFiniteLength_of_support_subset _ _ (Module.length_ne_top_iff.mp hlength) (by
            simp only [support_tensorProduct, Module.support_of_exact he hf hg]
            exact fun p hp ↦ ⟨Or.inl hp.1, hp.2⟩))
        have h₃ : Module.length R (L₃ ⊗[R] N) ≠ ⊤ := Module.length_ne_top_iff.mpr
          (isFiniteLength_of_support_subset _ _ (Module.length_ne_top_iff.mp hlength) (by
            simp only [support_tensorProduct, Module.support_of_exact he hf hg]
            exact fun p hp ↦ ⟨Or.inr hp.1, hp.2⟩))
        have hd₁ : Module.supportDim R L₁ + Module.supportDim R N ≤ ringKrullDim R :=
          (add_le_add (Module.supportDim_le_of_injective f hf) le_rfl).trans hd.le
        have hd₃ : Module.supportDim R L₃ + Module.supportDim R N ≤ ringKrullDim R :=
          (add_le_add (Module.supportDim_le_of_surjective g hg) le_rfl).trans hd.le
        have hn₁ : 0 ≤ chi R L₁ N := by
          rcases hd₁.eq_or_lt with hd₁ | hd₁
          · exact (ih₁ h₁ hd₁).le
          · rw [Inputs.intersectionVanishing R L₁ N h₁ hd₁]
        have hn₃ : 0 ≤ chi R L₃ N := by
          rcases hd₃.eq_or_lt with hd₃ | hd₃
          · exact (ih₃ h₃ hd₃).le
          · rw [Inputs.intersectionVanishing R L₃ N h₃ hd₃]
        rw [chi_add_left L₁ L₂ L₃ N f g hf hg he hlength]
        rw [supportDim_eq_max_of_exact f g hf hg he] at hd
        rcases le_total (Module.supportDim R L₁) (Module.supportDim R L₃) with hle | hle
        · rw [max_eq_right hle] at hd
          exact add_pos_of_nonneg_of_pos hn₁ (ih₃ h₃ hd)
        · rw [max_eq_left hle] at hd
          exact add_pos_of_pos_of_nonneg (ih₁ h₁ hd) hn₃
  exact hforall M hfin hdim

/-- 両変数が素イデアル商である場合の正値性から、任意の有限生成加群の正値性へ移す。 -/
theorem chi_pos_of_prime_quotients
    (hprime : ∀ (P Q : Ideal R) [P.IsPrime] [Q.IsPrime],
      Module.length R ((R ⧸ P) ⊗[R] (R ⧸ Q)) ≠ ⊤ →
      ringKrullDim (R ⧸ P) + ringKrullDim (R ⧸ Q) = ringKrullDim R →
      0 < chi R (R ⧸ P) (R ⧸ Q))
    (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N]
    (hfin : Module.length R (M ⊗[R] N) ≠ ⊤)
    (hdim : Module.supportDim R M + Module.supportDim R N = ringKrullDim R) :
    0 < chi R M N := by
  refine chi_pos_of_prime_left M N (fun P _ hf hd ↦ ?_) hfin hdim
  rw [chi_comm]
  refine chi_pos_of_prime_left N (R ⧸ P) (fun Q _ hq hqd ↦ ?_) ?_ ?_
  · exact hprime Q P hq (by simpa only [Module.supportDim_quotient_eq_ringKrullDim] using hqd)
  · rwa [← (TensorProduct.comm R (R ⧸ P) N).length_eq]
  · simpa only [Module.supportDim_quotient_eq_ringKrullDim, add_comm] using hd

end SerrePositivity
