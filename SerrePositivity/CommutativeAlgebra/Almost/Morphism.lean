module

public import SerrePositivity.CommutativeAlgebra.Almost.Zero

/-!
# 線形写像の almost 単射・全射・同型

核と余核が `I` に消される条件を、個々の線形写像に対して定義する。
二つの almost 単射・全射の合成は `I²` に関して同じ条件を満たすため、
`I²=I` の場合には合成で閉じる。ここでの単一写像の条件と、局所化した圏で
二つの対象が同型であることは別の主張であり、同一視しない。
-/

@[expose] public section

universe u v w z

namespace SerrePositivity.Almost

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]
variable {L : Type z} [AddCommGroup L] [Module R L]

/-- 線形写像の核が `I` に消されること。 -/
def IsAlmostInjective (I : Ideal R) (f : M →ₗ[R] N) : Prop := IsAlmostZero I f.ker

/-- 線形写像の余核が `I` に消されること。 -/
def IsAlmostSurjective (I : Ideal R) (f : M →ₗ[R] N) : Prop :=
  IsAlmostZero I (N ⧸ f.range)

/-- 個々の線形写像の核と余核がともに `I` に消されること。
局所化した圏での対象の同型関係そのものの定義ではない。 -/
def IsAlmostIso (I : Ideal R) (f : M →ₗ[R] N) : Prop :=
  IsAlmostInjective I f ∧ IsAlmostSurjective I f

namespace IsAlmostInjective

variable {I : Ideal R} {f : M →ₗ[R] N} {g : N →ₗ[R] L}

/-- almost 単射の条件を、核の元に対する作用として書く。 -/
theorem iff_smul_eq_zero :
    IsAlmostInjective I f ↔ ∀ x : M, f x = 0 → ∀ a ∈ I, a • x = 0 := by
  constructor
  · intro hf x hx a ha
    exact congrArg Subtype.val (hf.smul_eq_zero ha (⟨x, hx⟩ : f.ker))
  · intro hf
    apply IsAlmostZero.iff_smul_eq_zero.mpr
    intro a ha x
    exact Subtype.ext (hf x.1 x.2 a ha)

/-- almost 単射の核を `I` の元は消す。 -/
theorem smul_eq_zero (hf : IsAlmostInjective I f) (x : M) (hx : f x = 0)
    {a : R} (ha : a ∈ I) : a • x = 0 := iff_smul_eq_zero.mp hf x hx a ha

/-- 通常の単射は任意のイデアルに関して almost 単射。 -/
theorem of_injective (f : M →ₗ[R] N) (hf : Function.Injective f) : IsAlmostInjective I f := by
  apply iff_smul_eq_zero.mpr
  intro x hx a _
  have hx0 : x = 0 := hf (hx.trans f.map_zero.symm)
  rw [hx0, smul_zero]

/-- almost 単射の合成の核は `I²` に消される。 -/
theorem comp_mul (hf : IsAlmostInjective I f) (hg : IsAlmostInjective I g) :
    IsAlmostInjective (I * I) (g.comp f) := by
  change I * I ≤ Module.annihilator R (g.comp f).ker
  apply Ideal.mul_le.mpr
  intro a ha b hb
  rw [Module.mem_annihilator]
  intro x
  apply Subtype.ext
  change (a * b) • (x : M) = 0
  have hx : g (f (x : M)) = 0 := x.2
  have hbf : f (b • (x : M)) = 0 := by
    rw [f.map_smul, hg.smul_eq_zero (f x) hx hb]
  rw [mul_smul, hf.smul_eq_zero _ hbf ha]

/-- `I²=I` なら almost 単射は合成で閉じる。 -/
theorem comp (hI : I * I = I) (hf : IsAlmostInjective I f) (hg : IsAlmostInjective I g) :
    IsAlmostInjective I (g.comp f) := by simpa only [hI] using comp_mul hf hg

end IsAlmostInjective

namespace IsAlmostSurjective

variable {I : Ideal R} {f : M →ₗ[R] N} {g : N →ₗ[R] L}

/-- almost 全射とは `I` 倍した任意の元が写像の像に入ること。 -/
theorem iff_smul_mem_range :
    IsAlmostSurjective I f ↔ ∀ a ∈ I, ∀ y : N, a • y ∈ f.range := by
  constructor
  · intro hf a ha y
    have hz := hf.smul_eq_zero ha (Submodule.Quotient.mk y : N ⧸ f.range)
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hz
    exact hz
  · intro hf
    apply IsAlmostZero.iff_smul_eq_zero.mpr
    intro a ha y
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective f.range y
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact hf a ha y

/-- almost 全射では、`I` 倍した元は写像の像に入る。 -/
theorem smul_mem_range (hf : IsAlmostSurjective I f) {a : R} (ha : a ∈ I) (y : N) :
    a • y ∈ f.range := iff_smul_mem_range.mp hf a ha y

/-- 通常の全射は任意のイデアルに関して almost 全射。 -/
theorem of_surjective (f : M →ₗ[R] N) (hf : Function.Surjective f) : IsAlmostSurjective I f := by
  apply iff_smul_mem_range.mpr
  intro a _ y
  exact hf (a • y)

/-- almost 全射の合成の余核は `I²` に消される。 -/
theorem comp_mul (hf : IsAlmostSurjective I f) (hg : IsAlmostSurjective I g) :
    IsAlmostSurjective (I * I) (g.comp f) := by
  change I * I ≤ Module.annihilator R (L ⧸ (g.comp f).range)
  apply Ideal.mul_le.mpr
  intro a ha b hb
  rw [Module.mem_annihilator]
  intro y
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (g.comp f).range y
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  obtain ⟨n, hn⟩ := hg.smul_mem_range hb y
  obtain ⟨m, hm⟩ := hf.smul_mem_range ha n
  refine ⟨m, ?_⟩
  rw [LinearMap.comp_apply, hm, g.map_smul, hn, mul_smul]

/-- `I²=I` なら almost 全射は合成で閉じる。 -/
theorem comp (hI : I * I = I) (hf : IsAlmostSurjective I f) (hg : IsAlmostSurjective I g) :
    IsAlmostSurjective I (g.comp f) := by simpa only [hI] using comp_mul hf hg

end IsAlmostSurjective

namespace IsAlmostIso

variable {I : Ideal R} {f : M →ₗ[R] N} {g : N →ₗ[R] L}

/-- 通常の全単射な線形写像は almost 同型条件を満たす。 -/
theorem of_bijective (f : M →ₗ[R] N) (hf : Function.Bijective f) : IsAlmostIso I f :=
  ⟨IsAlmostInjective.of_injective f hf.1, IsAlmostSurjective.of_surjective f hf.2⟩

/-- 恒等写像は任意のイデアルに関して almost 同型条件を満たす。 -/
theorem refl (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] :
    IsAlmostIso I (LinearMap.id (R := R) (M := M)) :=
  of_bijective _ Function.bijective_id

/-- 線形同型は、核と余核による almost 同型条件を満たす。 -/
theorem of_equiv (e : M ≃ₗ[R] N) : IsAlmostIso I e.toLinearMap := of_bijective _ e.bijective

/-- 二つの almost 同型写像の合成は `I²` に関して almost 同型条件を満たす。 -/
theorem comp_mul (hf : IsAlmostIso I f) (hg : IsAlmostIso I g) :
    IsAlmostIso (I * I) (g.comp f) :=
  ⟨IsAlmostInjective.comp_mul hf.1 hg.1, IsAlmostSurjective.comp_mul hf.2 hg.2⟩

/-- `I²=I` なら almost 同型写像は合成で閉じる。 -/
theorem comp (hI : I * I = I) (hf : IsAlmostIso I f) (hg : IsAlmostIso I g) :
    IsAlmostIso I (g.comp f) := by simpa only [hI] using comp_mul hf hg

end IsAlmostIso

end SerrePositivity.Almost
