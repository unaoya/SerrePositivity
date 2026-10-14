module

public import SerrePositivity.CommutativeAlgebra.PerfectoidRootTorsion
public import SerrePositivity.CommutativeAlgebra.PerfectoidIdealPowers

/-! # pねじれを除く商とperfectoidイデアルの比較

pねじれのイデアルを実際に定義し、その商のpの非零因子性を証明する。
商がperfectoidであることは別の条件として明示し、普遍性による比較に必要な境界を保つ。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity

/-- pで消える元のイデアル。 -/
def pTorsionIdeal (S : Type u) [CommRing S] (p : ℕ) : Ideal S where
  carrier := {x | (p : S) * x = 0}
  zero_mem' := mul_zero _
  add_mem' := by
    intro a b ha hb
    change (p : S) * a = 0 at ha
    change (p : S) * b = 0 at hb
    change (p : S) * (a + b) = 0
    rw [mul_add, ha, hb, add_zero]
  smul_mem' := by
    intro a b hb
    change (p : S) * b = 0 at hb
    change (p : S) * (a * b) = 0
    rw [mul_left_comm, hb, mul_zero]

@[simp] theorem mem_pTorsionIdeal (S : Type u) [CommRing S] (p : ℕ) (x : S) :
    x ∈ pTorsionIdeal S p ↔ (p : S) * x = 0 := Iff.rfl

/-- perfectoid環のpねじれを除いた商では、pは非零因子として作用する。 -/
theorem IsIntegralPerfectoid.pTorsionQuotient_p_mul_injective
    (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime] (hS : IsIntegralPerfectoid S p) :
    Function.Injective (fun x : S ⧸ pTorsionIdeal S p ↦ (p : S ⧸ pTorsionIdeal S p) * x) := by
  have hzero (x : S ⧸ pTorsionIdeal S p) (hx : (p : S ⧸ pTorsionIdeal S p) * x = 0) :
      x = 0 := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hx' : (p : S) * ((p : S) * x) = 0 := by
      apply (mem_pTorsionIdeal S p _).mp
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [map_mul, map_natCast]
      exact hx
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact hS.p_mul_eq_zero_of_pow_mul_eq_zero S p 2 x
      (by simpa only [pow_two, mul_assoc] using hx')
  intro x y hxy
  dsimp only at hxy
  apply sub_eq_zero.mp
  apply hzero
  rw [mul_sub, hxy, sub_self]

/-- 任意の商でもmod pのFrobeniusの全射性は引き継がれる。完備性やFontaine核は別途必要。 -/
theorem IsIntegralPerfectoid.surjective_pow_mod_p_quotient
    (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime] (hS : IsIntegralPerfectoid S p)
    (I : Ideal S) :
    Function.Surjective (fun x : (S ⧸ I) ⧸ Ideal.span {(p : S ⧸ I)} ↦ x ^ p) := by
  rcases hS with hsub | ⟨_, _, _, hF, _⟩
  · let : Subsingleton S := hsub
    intro x
    exact ⟨0, Subsingleton.elim _ _⟩
  · let q := Ideal.Quotient.mk I
    have hmap : Ideal.span {(p : S)} ≤ (Ideal.span {(p : S ⧸ I)}).comap q := by
      rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
      exact Ideal.subset_span (Set.mem_singleton _)
    let f := Ideal.quotientMap (Ideal.span {(p : S ⧸ I)}) q hmap
    have hf : Function.Surjective f := Ideal.quotientMap_surjective Ideal.Quotient.mk_surjective
    intro x
    obtain ⟨y, hy⟩ := hf x
    obtain ⟨z, hz⟩ := hF y
    refine ⟨f z, ?_⟩
    change (f z) ^ p = x
    change z ^ p = y at hz
    rw [← map_pow, hz, hy]

/-- perfectoidなpねじれ商があれば、p^c g'で消える射からg'のperfectoidイデアルの像はpねじれ。
商のperfectoid性を単にpの非零因子性から推論しない。 -/
theorem perfectoidIdeal_image_p_mul_eq_zero_of_torsionQuotient_perfectoid
    (R S : Type u) [CommRing R] [CommRing S] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (hS : IsIntegralPerfectoid S p)
    (hQ : IsIntegralPerfectoid (S ⧸ pTorsionIdeal S p) p)
    (f : R →+* S) (g' : R) (c : ℕ) (hg : (p : S) ^ c * f g' = 0)
    (x : R) (hx : x ∈ perfectoidIdeal R p hR g') : (p : S) * f x = 0 := by
  let : Algebra.FinitePresentation R (R ⧸ Ideal.span {g'}) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton g')
  let q := Ideal.Quotient.mk (pTorsionIdeal S p)
  have hfg : g' ∈ RingHom.ker (q.comp f) := by
    change q (f g') = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (hS.p_mul_eq_zero_of_pow_mul_eq_zero S p c (f g') hg)
  let k : R ⧸ Ideal.span {g'} →+* S ⧸ pTorsionIdeal S p :=
    Ideal.Quotient.lift _ (q.comp f) ((Ideal.span_singleton_le_iff_mem _).mpr hfg)
  let hu := isPerfectoidization_toPerfectoidization R (R ⧸ Ideal.span {g'}) p hR
  have he := RingHom.congr_fun (IsPerfectoidization.lift_comp hu hQ k)
    (Ideal.Quotient.mk (Ideal.span {g'}) x)
  change toPerfectoidization R (R ⧸ Ideal.span {g'}) p hR
    (Ideal.Quotient.mk (Ideal.span {g'}) x) = 0 at hx
  rw [RingHom.comp_apply, hx, map_zero] at he
  exact Ideal.Quotient.eq_zero_iff_mem.mp he.symm

end SerrePositivity
