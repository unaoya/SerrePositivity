module

public import SerrePositivity.CommutativeAlgebra.PerfectoidizationFunctor
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Torsion
public import Mathlib.RingTheory.Ideal.Maps

/-! # Universal perfectoidization is invariant under surjections with nil kernel

The induced comparison itself is bijective and retains the original unit diagram.
No uniform nilpotence exponent, finiteness, or completeness of the source is needed.
This handles nilpotent modifications, not arbitrary integral modifications away from g.
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.IsPerfectoidization
variable {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    {p : ℕ} [Fact p.Prime]

/-- A universal perfectoidization remains universal after precomposition with a
surjection whose kernel consists of nilpotent elements. -/
theorem precomp_surjective_nil_kernel {f : B →+* C}
    (hf : IsPerfectoidization p f) (q : A →+* B) (hq : Function.Surjective q)
    (hnil : ∀ x ∈ RingHom.ker q, IsNilpotent x) :
    IsPerfectoidization p (f.comp q) := by
  refine ⟨hf.1, ?_⟩
  intro T _ hT k
  let := hT.isReduced T p
  have hk : RingHom.ker q ≤ RingHom.ker k := by
    intro x hx
    exact IsReduced.eq_zero _ ((hnil x hx).map k)
  let l : B →+* T := q.liftOfSurjective hq ⟨k, hk⟩
  have hl : l.comp q = k := q.liftOfSurjective_comp hq ⟨k, hk⟩
  obtain ⟨m, hm, huniq⟩ := hf.2 T hT l
  refine ⟨m, ?_, ?_⟩
  · change m.comp (f.comp q) = k
    rw [← RingHom.comp_assoc, hm, hl]
  · intro n hn
    apply huniq
    apply RingHom.ext
    intro b
    obtain ⟨a, rfl⟩ := hq b
    have hna := RingHom.congr_fun hn a
    have hla := RingHom.congr_fun hl a
    exact hna.trans hla.symm

/-- Chosen universal perfectoidizations across a nil-kernel surjection have an
actual ring equivalence preserving the original source map. -/
theorem exists_equiv_of_surjective_nil_kernel {f : A →+* C} {g : B →+* D}
    (hf : IsPerfectoidization p f) (hg : IsPerfectoidization p g)
    (q : A →+* B) (hq : Function.Surjective q)
    (hnil : ∀ x ∈ RingHom.ker q, IsNilpotent x) :
    ∃ e : C ≃+* D, e.toRingHom.comp f = g.comp q :=
  hf.exists_equiv p (hg.precomp_surjective_nil_kernel q hq hnil)

/-- The original functorial comparison, not merely some comparison, is bijective. -/
theorem map_bijective_of_surjective_nil_kernel {f : A →+* C} {g : B →+* D}
    (hf : IsPerfectoidization p f) (hg : IsPerfectoidization p g)
    (q : A →+* B) (hq : Function.Surjective q)
    (hnil : ∀ x ∈ RingHom.ker q, IsNilpotent x) :
    Function.Bijective (map hf hg q) := by
  obtain ⟨e, he⟩ := hf.exists_equiv_of_surjective_nil_kernel hg q hq hnil
  have hmap : e.toRingHom = map hf hg q := hf.lift_unique hg.1 (g.comp q) e.toRingHom he
  rw [← hmap]
  exact e.bijective

/-- Quotient ideals with the same radical induce a bijection on their chosen
perfectoidizations. The comparison is the one induced by the actual quotient map. -/
theorem map_bijective_quotient_of_le_radical
    (R : Type u) [CommRing R] (I J : Ideal R) (hIJ : I ≤ J) (hJI : J ≤ I.radical)
    {f : R ⧸ I →+* C} {g : R ⧸ J →+* D}
    (hf : IsPerfectoidization p f) (hg : IsPerfectoidization p g) :
    Function.Bijective (map hf hg (Ideal.Quotient.factor hIJ)) := by
  apply hf.map_bijective_of_surjective_nil_kernel hg
  · intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk I x, rfl⟩
  · intro y hy
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hx : x ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp hy
    obtain ⟨n, hn⟩ := hJI hx
    refine ⟨n, ?_⟩
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hn

end SerrePositivity.IsPerfectoidization
