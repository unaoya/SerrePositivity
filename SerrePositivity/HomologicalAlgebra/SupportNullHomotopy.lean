module

public import SerrePositivity.HomologicalAlgebra.NullHomotopy
public import Mathlib.RingTheory.Support

/-! # 幾何学的支持から有限射影複体の零ホモトピーを構成する

一般の可換環では perfect 複体のホモロジーは有限生成とは限らない。
各項からホモロジーへの有限生成な像だけを冪で消し、上の次数から順に消去する。
-/

@[expose] public section

universe u

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [CommRing R]

/-- 支持が `V(r)` に入る加群への有限生成加群からの射は、`r` のある冪で消える。 -/
lemma exists_pow_smul_map_eq_zero_of_support
    {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] (f : M →ₗ[R] N) (r : R)
    (hN : Module.support R N ⊆ PrimeSpectrum.zeroLocus {r}) :
    ∃ n : ℕ, r ^ n • f = 0 := by
  have h := (Module.support_subset_of_injective f.range.subtype
    f.range.subtype_injective).trans hN
  rw [Module.support_eq_zeroLocus, ← PrimeSpectrum.zeroLocus_span {r},
    PrimeSpectrum.zeroLocus_subset_zeroLocus_iff] at h
  obtain ⟨n, hn⟩ := h (Ideal.subset_span (Set.mem_singleton r))
  refine ⟨n, ?_⟩
  ext x
  exact congrArg Subtype.val ((Module.mem_annihilator.mp hn) ⟨f x, LinearMap.mem_range_self f x⟩)

set_option backward.isDefEq.respectTransparency.types false in
/-- ホモロジーの支持条件と有限射影性により、ある冪を掛けた射の一段を消去できる。 -/
lemma clear_degree_of_homology_support (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (r : R) (k : ℤ) [Module.Finite R (P.X k)] [Projective (P.X k)]
    (f : P ⟶ P) (hf : ∀ i, k < i → f.f i = 0)
    (hr : Module.support R (P.homology k) ⊆ PrimeSpectrum.zeroLocus {r}) :
    ∃ n : ℕ, ∃ g : P ⟶ P, (∀ i, k ≤ i → g.f i = 0) ∧
      (homotopyQuot R).map g = r ^ n • (homotopyQuot R).map f := by
  let S := P.sc' (k - 1) k (k + 1)
  let e : P.homology k ≅ S.homology :=
    P.homologyIsoSc' (k - 1) k (k + 1)
      (by simp [CochainComplex.prev]) (by simp [CochainComplex.next])
  have hrS : Module.support R S.homology ⊆ PrimeSpectrum.zeroLocus {r} := by
    rw [← e.toLinearEquiv.support_eq]
    exact hr
  have hcycle : f.f k ≫ S.g = 0 := by
    change f.f k ≫ P.d k (k + 1) = 0
    rw [f.comm k (k + 1), hf (k + 1) (by omega), comp_zero]
  let u := S.liftCycles (f.f k) hcycle
  obtain ⟨n, hn⟩ := exists_pow_smul_map_eq_zero_of_support (u ≫ S.homologyπ).hom r hrS
  let B := ShortComplex.mk S.toCycles S.homologyπ S.toCycles_comp_homologyπ
  have hB : B.Exact := B.exact_of_g_is_cokernel S.homologyIsCokernel
  have hru : (r ^ n • u) ≫ S.homologyπ = 0 := by
    rw [Linear.smul_comp]
    exact ModuleCat.hom_ext hn
  let h := hB.liftFromProjective (r ^ n • u) hru
  have hh : h ≫ P.d (k - 1) k = r ^ n • f.f k := by
    change h ≫ S.f = r ^ n • f.f k
    rw [← S.toCycles_i, ← Category.assoc, hB.liftFromProjective_comp,
      Linear.smul_comp, S.liftCycles_i]
  exact ⟨n, clear_degree_of_factorization P (r ^ n) k f hf h hh⟩

/-- 有界有限射影複体のホモロジーの支持が `V(r)` に入れば、`r` の冪は零ホモトピック。
ホモロジーの有限生成性・環の Noether 性は仮定しない。 -/
theorem exists_pow_nullHomotopy_of_homology_support
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (r : R)
    (hfinite : ∀ i, Module.Finite R (P.X i)) (hproj : ∀ i, Projective (P.X i))
    (hbound : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (P.X i))
    (hr : ∀ i, Module.support R (P.homology i) ⊆ PrimeSpectrum.zeroLocus {r}) :
    ∃ n : ℕ, Nonempty (Homotopy (r ^ n • 𝟙 P) 0) := by
  obtain ⟨a, b, hab⟩ := hbound
  have step : ∀ m : ℕ, ∃ n : ℕ, ∃ f : P ⟶ P,
      (∀ i, b - (m : ℤ) < i → f.f i = 0) ∧
        (homotopyQuot R).map f = r ^ n • 𝟙 ((homotopyQuot R).obj P) := by
    intro m
    induction m with
    | zero =>
      refine ⟨0, 𝟙 P, ?_, by simp⟩
      intro i hi
      exact (hab i (Or.inr (by simpa using hi))).eq_of_src _ _
    | succ m ih =>
      obtain ⟨n, f, hf, hclass⟩ := ih
      have := hfinite (b - (m : ℤ))
      have := hproj (b - (m : ℤ))
      obtain ⟨v, g, hg, hgc⟩ := clear_degree_of_homology_support P r (b - (m : ℤ)) f hf (hr _)
      refine ⟨v + n, g, fun i hi ↦ hg i (by push_cast at hi; omega), ?_⟩
      rw [hgc, hclass, ← mul_smul, ← pow_add]
  obtain ⟨n, f, hf, hc⟩ := step (b - a + 1).toNat
  have hzero : f = 0 := by
    apply HomologicalComplex.hom_ext
    intro i
    by_cases hi : i < a
    · exact (hab i (Or.inl hi)).eq_of_src _ _
    · exact hf i (by omega)
  refine ⟨n, (nonempty_homotopy_smul_id_zero_iff _ P).mpr ?_⟩
  rw [← hc, hzero, Functor.map_zero]

end SerrePositivity
