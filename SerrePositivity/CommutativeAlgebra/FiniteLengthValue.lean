module

public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.Algebra.Exact.Basic

/-! # 有限長を自然数へ移す共通 API

有限性を確認してから `ENat.toNat` を加法性に通す。
整数・有理数・実数への埋め込みは、この自然数値の等式から導く。
環の局所性・Noether 性は要求しない。
-/

@[expose] public section
universe u
namespace SerrePositivity
variable {R : Type u} [CommRing R]

/-- 短完全列の自然数値の長さ。中央の有限長性から両端の有限性も得る。 -/
lemma lengthNat_add_of_exact {M N P : Type u}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hf : Function.Injective f) (hg : Function.Surjective g) (he : Function.Exact f g)
    (hN : IsFiniteLength R N) :
    (Module.length R N).toNat = (Module.length R M).toNat + (Module.length R P).toNat := by
  rw [Module.length_eq_add_of_exact f g hf hg he,
    ENat.toNat_add (Module.length_ne_top_iff.mpr (hN.of_injective hf))
      (Module.length_ne_top_iff.mpr (hN.of_surjective hg))]

/-- 有限長加群の長さは、核と像の長さの和。 -/
lemma lengthNat_ker_add_range {M N : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (hM : IsFiniteLength R M) :
    (Module.length R M).toNat = (Module.length R f.ker).toNat +
      (Module.length R f.range).toNat := by
  have h := lengthNat_add_of_exact f.ker.subtype f.ker.mkQ
    (Submodule.subtype_injective _) (Submodule.mkQ_surjective _)
    (LinearMap.exact_subtype_mkQ f.ker) hM
  rwa [f.quotKerEquivRange.length_eq] at h

/-- 完全列の有限長な中央の長さは、前後の像の長さの和。 -/
lemma lengthNat_eq_add_range {M N P : Type u}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (he : Function.Exact f g) (hN : IsFiniteLength R N) :
    (Module.length R N).toNat = (Module.length R f.range).toNat +
      (Module.length R g.range).toNat := by
  rw [lengthNat_ker_add_range g hN, ← LinearMap.exact_iff.mp he]

end SerrePositivity
