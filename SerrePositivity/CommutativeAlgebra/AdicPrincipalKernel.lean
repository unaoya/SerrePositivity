module

public import SerrePositivity.CommutativeAlgebra.Adic.Complete

/-! # 飽和したイデアルの生成元をadic商から持ち上げる

剰余の生成元と飽和性から、完備性によって元のイデアルの生成元を同定する。
Noether性・イデアルの有限生成性・イデアル自身の完備性を要求しない。
-/

public section
namespace SerrePositivity
variable {R S : Type*} [CommRing R] [CommRing S]

/-- aで飽和したイデアルは、mod aで生成する一元によって生成される。 -/
theorem ideal_eq_span_of_saturated_of_mod_generator (a : R)
    [IsAdicComplete (Ideal.span {a}) R] (J : Ideal R) (ξ : R) (hξ : ξ ∈ J)
    (hsat : ∀ x : R, a * x ∈ J → x ∈ J)
    (hgen : ∀ x : R, x ∈ J → ∃ r : R, x - ξ * r ∈ Ideal.span {a}) :
    J = Ideal.span {ξ} := by
  let I := Ideal.span {a}
  let f : R →ₗ[R] J := (LinearMap.mulLeft R ξ).codRestrict J
    (fun r ↦ J.mul_mem_right r hξ)
  let := isHausdorff_of_injective_linearMap I J.subtype Subtype.val_injective
  have hf : Function.Surjective f := by
    apply surjective_of_mkQ_comp_surjective (I := I)
    intro z
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R J)) z
    obtain ⟨r, hr⟩ := hgen x x.property
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hr
    have hyJ : y ∈ J := hsat y (by
      rw [← hy]
      exact J.sub_mem x.property (J.mul_mem_right r hξ))
    have hdiff : x - f r ∈ I • (⊤ : Submodule R J) := by
      have he : x - f r = a • (⟨y, hyJ⟩ : J) := by
        apply Subtype.ext
        exact hy
      rw [he]
      exact Submodule.smul_mem_smul (Ideal.subset_span (Set.mem_singleton _))
        (Submodule.mem_top : (⟨y, hyJ⟩ : J) ∈ (⊤ : Submodule R J))
    refine ⟨r, ?_⟩
    apply Eq.symm
    apply (Submodule.Quotient.eq _).mpr
    exact hdiff
  apply le_antisymm
  · intro x hx
    obtain ⟨r, hr⟩ := hf ⟨x, hx⟩
    exact Ideal.mem_span_singleton.mpr ⟨r, (congrArg Subtype.val hr).symm⟩
  · exact (Ideal.span_singleton_le_iff_mem _).mpr hξ

/-- 終域でaが非零因子なら環準同型の核はaで飽和している。 -/
theorem ker_eq_span_of_regular_of_mod_generator (a : R)
    [IsAdicComplete (Ideal.span {a}) R] (f : R →+* S)
    (hregular : Function.Injective (fun x : S ↦ f a * x))
    (ξ : R) (hξ : f ξ = 0)
    (hgen : ∀ x : R, f x = 0 → ∃ r : R, x - ξ * r ∈ Ideal.span {a}) :
    RingHom.ker f = Ideal.span {ξ} := by
  apply ideal_eq_span_of_saturated_of_mod_generator a (RingHom.ker f) ξ hξ
  · intro x hx
    change f (a * x) = 0 at hx
    change f x = 0
    apply hregular
    simpa only [map_mul, mul_zero] using hx
  · exact hgen

end SerrePositivity
