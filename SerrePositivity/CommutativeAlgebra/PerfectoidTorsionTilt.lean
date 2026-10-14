module

public import SerrePositivity.CommutativeAlgebra.PerfectionKernelLift
public import SerrePositivity.CommutativeAlgebra.PerfectoidTorsionFrobenius

/-! # pねじれ商のmod p写像とtiltの第0射影の核

mod p写像の核内で根を取れることを確認し、perfectionの持ち上げを適用する。
untiltの自然性とFontaine核への最終接続は別の工程とする。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
variable (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime]

/-- pねじれ商へのmod pの標準写像。 -/
def pTorsionQuotientModPMap : ModP S p →+* ModP (S ⧸ pTorsionIdeal S p) p :=
  Ideal.quotientMap (Ideal.span {(p : S ⧸ pTorsionIdeal S p)})
    (Ideal.Quotient.mk (pTorsionIdeal S p)) (by
      rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
      exact Ideal.subset_span (Set.mem_singleton _))

omit [Fact p.Prime] in
@[simp] theorem pTorsionQuotientModPMap_apply (x : S) :
    pTorsionQuotientModPMap S p (Ideal.Quotient.mk (Ideal.span {(p : S)}) x) =
      Ideal.Quotient.mk (Ideal.span {(p : S ⧸ pTorsionIdeal S p)})
        (Ideal.Quotient.mk (pTorsionIdeal S p) x) := rfl

omit [Fact p.Prime] in
theorem pTorsionQuotientModPMap_surjective : Function.Surjective (pTorsionQuotientModPMap S p) :=
  Ideal.quotientMap_surjective Ideal.Quotient.mk_surjective

/-- mod p写像の核の元には、その核の中でp乗根が存在する。 -/
theorem IsIntegralPerfectoid.pTorsionQuotientModPMap_kernel_roots
    (hS : IsIntegralPerfectoid S p) (a : ModP S p)
    (ha : pTorsionQuotientModPMap S p a = 0) :
    ∃ b : ModP S p, pTorsionQuotientModPMap S p b = 0 ∧ b ^ p = a := by
  let q := Ideal.Quotient.mk (pTorsionIdeal S p)
  let k := Ideal.Quotient.mk (Ideal.span {(p : S)})
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hx : q x ∈ Ideal.span {(p : S ⧸ pTorsionIdeal S p)} :=
    Ideal.Quotient.eq_zero_iff_mem.mp ha
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hx
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
  let t := x - (p : S) * c
  have ht : (p : S) * t = 0 := by
    apply (mem_pTorsionIdeal S p t).mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q (x - (p : S) * c) = 0
    rw [map_sub, map_mul, map_natCast, hc, sub_self]
  obtain ⟨y, hy, hyp⟩ := hS.exists_p_torsion_p_root S p t ht
  have hqy : q y = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hy
  have hkp : k (p : S) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have htx : k t = k x := by
    dsimp only [t]
    rw [map_sub, map_mul, hkp, zero_mul, sub_zero]
  refine ⟨k y, ?_, ?_⟩
  · rw [pTorsionQuotientModPMap_apply]
    change Ideal.Quotient.mk (Ideal.span {(p : S ⧸ pTorsionIdeal S p)}) (q y) = 0
    rw [hqy, map_zero]
  · rw [← map_pow, hyp, htx]

variable [Fact (¬ IsUnit (p : S))]
    [Fact (¬ IsUnit (p : S ⧸ pTorsionIdeal S p))]

/-- 元のtiltからpねじれ商のtiltへの写像は全射。 -/
theorem IsIntegralPerfectoid.pTorsionQuotient_preTiltMap_surjective
    (hS : IsIntegralPerfectoid S p) :
    Function.Surjective (Perfection.map p (pTorsionQuotientModPMap S p)) :=
  perfection_map_surjective_of_kernel_roots p (pTorsionQuotientModPMap S p)
    (pTorsionQuotientModPMap_surjective S p) (hS.pTorsionQuotientModPMap_kernel_roots S p)

/-- pねじれ商のtiltの第0射影の核は、元の第0射影の核の像である。 -/
theorem IsIntegralPerfectoid.pTorsionQuotient_preTilt_coeff_kernel
    (hS : IsIntegralPerfectoid S p) :
    (RingHom.ker (PreTilt.coeff 0 : PreTilt S p →+* ModP S p)).map
      (Perfection.map p (pTorsionQuotientModPMap S p)) =
      RingHom.ker (PreTilt.coeff 0 : PreTilt (S ⧸ pTorsionIdeal S p) p →+*
        ModP (S ⧸ pTorsionIdeal S p) p) :=
  perfection_map_coeff_zero_kernel p (pTorsionQuotientModPMap S p)
    (pTorsionQuotientModPMap_surjective S p) (hS.pTorsionQuotientModPMap_kernel_roots S p)

end SerrePositivity
