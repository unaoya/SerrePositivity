module

public import SerrePositivity.CommutativeAlgebra.PerfectoidTorsionQuotient
public import SerrePositivity.CommutativeAlgebra.PerfectoidTorsionRoots
public import SerrePositivity.CommutativeAlgebra.PerfectoidReduced

/-! # pねじれ商へのFrobenius核条件の移送

pねじれのp乗根を選んで誤差を除き、元のperfectoid環のFrobenius核条件を適用する。
商のFontaine核の単項性はこの移送だけからは主張しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity

/-- pねじれ商のFrobenius核は、元のp乗根の像で生成される。 -/
theorem IsIntegralPerfectoid.pTorsionQuotient_frobenius_kernel
    (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime] (hS : IsIntegralPerfectoid S p)
    (π : S) (u : Sˣ) (hπ : (p : S) = u * π ^ p)
    (x : S ⧸ pTorsionIdeal S p)
    (hx : x ^ p ∈ Ideal.span {(p : S ⧸ pTorsionIdeal S p)}) :
    x ∈ Ideal.span {Ideal.Quotient.mk (pTorsionIdeal S p) π} := by
  rcases hS with hsub | hdata
  · let : Subsingleton S := hsub
    rw [Subsingleton.elim x 0]
    exact Ideal.zero_mem _
  have hS : IsIntegralPerfectoid S p := Or.inr hdata
  obtain ⟨hp, _, _⟩ := hdata
  let : Fact (¬ IsUnit (p : S)) := ⟨hp⟩
  let q := Ideal.Quotient.mk (pTorsionIdeal S p)
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hx
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  have ht : (p : S) * (x ^ p - (p : S) * b) = 0 := by
    apply (mem_pTorsionIdeal S p _).mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q (x ^ p - (p : S) * b) = 0
    rw [map_sub, map_pow, map_mul, map_natCast]
    exact sub_eq_zero.mpr hb
  obtain ⟨y, hy, hyp⟩ := hS.exists_p_torsion_p_root S p _ ht
  have hdiff : (x - y) ^ p ∈ Ideal.span {(p : S)} := by
    let k := Ideal.Quotient.mk (Ideal.span {(p : S)})
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change k ((x - y) ^ p) = 0
    rw [map_pow, map_sub, sub_pow_char, ← map_pow, ← map_pow, hyp,
      map_sub, map_mul, map_natCast]
    have hkp : k (p : S) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
    rw [show (p : S ⧸ Ideal.span {(p : S)} ) = 0 from by
      simpa only [map_natCast] using hkp, zero_mul, sub_zero, sub_self]
  have hm : x - y ∈ Ideal.span {π} :=
    hS.frobenius_kernel_of_unit_root S p π u hπ _ (by
      rwa [hπ, Ideal.span_singleton_mul_left_unit u.isUnit] at hdiff)
  have hqy : q y = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hy
  have hm' := Ideal.mem_map_of_mem q hm
  simpa only [Ideal.map_span, Set.image_singleton, map_sub, hqy, sub_zero] using hm'

/-- pねじれ商は被約。Fontaine核の単項性や商のperfectoid性を仮定しない。 -/
theorem IsIntegralPerfectoid.pTorsionQuotient_isReduced
    (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime] (hS : IsIntegralPerfectoid S p) :
    IsReduced (S ⧸ pTorsionIdeal S p) := by
  rcases hS with hsub | hdata
  · let : Subsingleton S := hsub
    exact ⟨fun _ _ ↦ Subsingleton.elim _ _⟩
  have hS : IsIntegralPerfectoid S p := Or.inr hdata
  obtain ⟨_, _, ⟨π, u, hπ⟩, _⟩ := hdata
  let Q := S ⧸ pTorsionIdeal S p
  let q := Ideal.Quotient.mk (pTorsionIdeal S p)
  let v : Qˣ := Units.map q.toMonoidHom u
  have hqπ : (p : Q) = v * (q π) ^ p := by
    change (p : Q) = q (u : S) * (q π) ^ p
    simpa only [map_mul, map_pow, map_natCast] using congrArg q hπ
  let := hS.pTorsionQuotient_isAdicComplete S p
  apply isReduced_of_regular_unit_root_frobenius_kernel Q p (Fact.out : p.Prime).one_lt
    (q π) v hqπ (hS.pTorsionQuotient_root_mul_injective S p (q π) v p
      (Fact.out : p.Prime).pos hqπ) inferInstance
  exact hS.pTorsionQuotient_frobenius_kernel S p π u hπ

/-- 整perfectoid環は被約。ねじれ商の被約性から冪零元をpねじれへ帰着する。 -/
theorem IsIntegralPerfectoid.isReduced
    (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime] (hS : IsIntegralPerfectoid S p) :
    IsReduced S := by
  let := hS.pTorsionQuotient_isReduced S p
  refine ⟨fun x hx ↦ ?_⟩
  let q := Ideal.Quotient.mk (pTorsionIdeal S p)
  have hq : q x = 0 := IsReduced.eq_zero _ (hx.map q)
  exact hS.eq_zero_of_p_mul_eq_zero_of_isNilpotent S p x
    (Ideal.Quotient.eq_zero_iff_mem.mp hq) hx

end SerrePositivity
