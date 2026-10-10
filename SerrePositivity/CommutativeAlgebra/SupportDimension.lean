module

public import SerrePositivity.CommutativeAlgebra.FiniteLength
public import Mathlib.RingTheory.KrullDimension.Module

/-! # 短完全列と台の次元

短完全列の中央の次元は両端の次元の最大値である。
台の素イデアル鎖は最小の素イデアルを含む側にすべて入る、という議論で証明する。
有限長テンソル積から、二つの素イデアルの和の根基が極大イデアルとなることも示す。
-/

public section

universe u

namespace SerrePositivity

open IsLocalRing TensorProduct

variable {R : Type u} [CommRing R]

/-- 短完全列の台の次元は両端の台の次元の最大値。有限生成性は不要。 -/
theorem supportDim_eq_max_of_exact
    {M₁ M₂ M₃ : Type u} [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
    [Module R M₁] [Module R M₂] [Module R M₃]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃)
    (hf : Function.Injective f) (hg : Function.Surjective g) (he : Function.Exact f g) :
    Module.supportDim R M₂ = max (Module.supportDim R M₁) (Module.supportDim R M₃) := by
  apply le_antisymm
  · unfold Module.supportDim Order.krullDim
    refine iSup_le fun c ↦ ?_
    have hc := (congrArg (fun s : Set (PrimeSpectrum R) ↦ c.head.val ∈ s)
      (Module.support_of_exact he hf hg)).mp c.head.property
    rcases hc with hc | hc
    · let c₁ : LTSeries (Module.support R M₁) := LTSeries.mk c.length
        (fun i ↦ ⟨(c i).val, Module.mem_support_mono (c.head_le i) hc⟩)
        (fun _ _ hij ↦ c.strictMono hij)
      exact (Order.LTSeries.length_le_krullDim c₁).trans (le_max_left _ _)
    · let c₃ : LTSeries (Module.support R M₃) := LTSeries.mk c.length
        (fun i ↦ ⟨(c i).val, Module.mem_support_mono (c.head_le i) hc⟩)
        (fun _ _ hij ↦ c.strictMono hij)
      exact (Order.LTSeries.length_le_krullDim c₃).trans (le_max_right _ _)
  · exact max_le (Module.supportDim_le_of_injective f hf)
      (Module.supportDim_le_of_surjective g hg)

/-- 局所環の二つの素イデアル商のテンソル積が有限長なら、その和の根基は極大イデアル。
テンソル積の台の交叉表示を使うため、テンソル積と商環の同型の選択を必要としない。 -/
theorem radical_sup_eq_maximalIdeal_of_tensor_finiteLength [IsLocalRing R]
    (P Q : Ideal R) [P.IsPrime] [Q.IsPrime]
    (hfin : Module.length R ((R ⧸ P) ⊗[R] (R ⧸ Q)) ≠ ⊤) :
    (P ⊔ Q).radical = maximalIdeal R := by
  apply le_antisymm
  · exact (Ideal.radical_mono
      (sup_le (le_maximalIdeal (Ideal.IsPrime.ne_top (inferInstance : P.IsPrime)))
        (le_maximalIdeal (Ideal.IsPrime.ne_top (inferInstance : Q.IsPrime))))).trans_eq
        (maximalIdeal.isMaximal R).isPrime.radical
  · rw [Ideal.radical_eq_sInf]
    refine le_sInf fun J hJ ↦ ?_
    obtain ⟨hPJQ, hJprime⟩ := hJ
    let := hJprime
    have hmem : (⟨J, hJprime⟩ : PrimeSpectrum R) ∈
        Module.support R ((R ⧸ P) ⊗[R] (R ⧸ Q)) := by
      rw [support_tensorProduct]
      constructor
      · exact Module.mem_support_iff_of_finite.mpr (by
          rw [Ideal.annihilator_quotient]
          exact le_sup_left.trans hPJQ)
      · exact Module.mem_support_iff_of_finite.mpr (by
          rw [Ideal.annihilator_quotient]
          exact le_sup_right.trans hPJQ)
    exact (eq_maximalIdeal (isMaximal_of_mem_support_of_isFiniteLength _
      (Module.length_ne_top_iff.mp hfin) _ hmem)).ge

end SerrePositivity
