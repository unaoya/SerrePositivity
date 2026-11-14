module

public import SerrePositivity.BhattScholze.Perfectoidization.Arc.Valuations.ArcValuationTilt
public import SerrePositivity.BhattScholze.Prism.Perfectoid.WittQuotientPerfectoid
public import Mathlib.RingTheory.KrullDimension.LocalRing
public import Mathlib.RingTheory.LocalRing.Quotient

/-!
# 階数 1 の付値環の untilt

## 概要
第零係数 a に沿って完備な階数 1 の完全付値環について、distinguished Witt 商は
p 完備な階数 1 の整 perfectoid 付値環となり、tilt は元の環に戻る。

## 方針
a が非零の場合、Witt 商の p 正則性と a 進分離性から、sharp は零を反映する。
剰余が非零の元を sharp の単元倍に書き、p の冪で割ることで全元に広げる。
付値環性の計算は Česnavičius–Scholze, Purity for flat cohomology, Proposition 2.1.9 に沿う。

## 規約
a が零の場合は、distinguished 元が p の単元倍なので、Witt 商は元の環と同型。

## 使われ方
BS 著者版 Proposition 8.10 の証明で、完全な試験付値環を untilt する。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

open IsLocalRing

variable (p : ℕ) [Fact p.Prime]
variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] [CharP V p] [PerfectRing V p]
variable (d : WittVector p V)

set_option quotPrecheck false in
local notation "U" => WittVector p V ⧸ Ideal.span {d}
local notation "d₀" => d.coeff 0

private def wittQuotientSharp : V →* U :=
  (Ideal.Quotient.mk (Ideal.span {d})).toMonoidHom.comp (WittVector.teichmuller p)

local notation "sharp" => wittQuotientSharp p d

omit [IsDomain V] [ValuationRing V] [CharP V p] [PerfectRing V p] in
private theorem wittQuotientSharp_zero : sharp 0 = 0 := by
  change Ideal.Quotient.mk (Ideal.span {d}) (WittVector.teichmuller p 0) = 0
  rw [WittVector.teichmuller_zero, map_zero]

omit [IsDomain V] [ValuationRing V] in
private theorem wittQuotientSharp_associated_p
    (hd : (wittDeltaStructure p V).IsDistinguished d) : Associated (p : U) (sharp d₀) := by
  obtain ⟨u, hu⟩ := exists_teichmuller_add_p_mul_unit_of_distinguished p V d hd
  let q := Ideal.Quotient.mk (Ideal.span {d})
  have he := congrArg q hu
  have hz : q d = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  rw [hz, map_add, map_mul, map_natCast] at he
  have ha : sharp d₀ = (p : U) * (-q (u : WittVector p V)) := by
    rw [mul_neg]
    exact eq_neg_of_add_eq_zero_left he.symm
  rw [ha]
  exact associated_mul_unit_right _ _ (u.isUnit.map q).neg

omit [IsDomain V] [ValuationRing V] in
private theorem wittQuotientSharp_modP (x : V) :
    wittQuotientModPEquiv p V d (Ideal.Quotient.mk (Ideal.span {(p : U)}) (sharp x)) =
      Ideal.Quotient.mk (Ideal.span {d₀}) x := by
  rw [show sharp x = Ideal.Quotient.mk (Ideal.span {d}) (WittVector.teichmuller p x) from rfl,
    wittQuotientModPEquiv_mk, WittVector.teichmuller_coeff_zero]

omit [Fact p.Prime] in
private theorem isLocalHom_mod_p_of_complete {S : Type*} [CommRing S]
    [IsAdicComplete (Ideal.span {(p : S)}) S] :
    IsLocalHom (Ideal.Quotient.mk (Ideal.span {(p : S)})) := by
  let P := Ideal.span {(p : S)}
  let q := Ideal.Quotient.mk P
  refine ⟨fun x hx => ?_⟩
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (↑hx.unit⁻¹ : S ⧸ P)
  have hxy : x * y - 1 ∈ P := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hu := hx.unit_spec
    rw [map_sub, map_mul, map_one, hy]
    apply sub_eq_zero.mpr
    calc
      q x * (↑hx.unit⁻¹ : S ⧸ P) = (↑hx.unit : S ⧸ P) * (↑hx.unit⁻¹ : S ⧸ P) :=
        congrArg (fun z : S ⧸ P => z * ↑hx.unit⁻¹) hu.symm
      _ = 1 := Units.mul_inv _
  have hu := Ideal.isUnit_of_sub_one_mem_jacobson_bot (x * y)
    (IsAdicComplete.le_jacobson_bot P hxy)
  exact isUnit_of_mul_isUnit_left hu

private theorem wittQuotientSharp_isUnit_iff (ha : ¬ IsUnit d₀)
    [IsAdicComplete (Ideal.span {(p : U)}) U] (x : V) :
    IsUnit (sharp x) ↔ IsUnit x := by
  let q := Ideal.Quotient.mk (Ideal.span {d₀})
  have hproper : (Ideal.span {d₀} : Ideal V) ≠ ⊤ :=
    fun h => ha (Ideal.span_singleton_eq_top.mp h)
  let : Nontrivial (V ⧸ Ideal.span {d₀}) := (Ideal.Quotient.nontrivial_iff).mpr hproper
  let : IsLocalHom q := IsLocalHom.of_surjective q Ideal.Quotient.mk_surjective
  refine ⟨fun hu => IsUnit.of_map q x ?_, fun hu => hu.map sharp⟩
  have h := (hu.map (Ideal.Quotient.mk (Ideal.span {(p : U)}))).map
    (wittQuotientModPEquiv p V d).toRingHom
  change IsUnit (wittQuotientModPEquiv p V d
    (Ideal.Quotient.mk (Ideal.span {(p : U)}) (sharp x))) at h
  rw [wittQuotientSharp_modP] at h
  exact h

omit [ValuationRing V] in
private theorem wittQuotientSharp_eq_zero_of_regular (ha : d₀ ≠ 0)
    (hd : (wittDeltaStructure p V).IsDistinguished d)
    [Fact (¬ IsUnit (p : U))] [IsAdicComplete (Ideal.span {(p : U)}) U]
    [IsAdicComplete (Ideal.span {d₀}) V] {x : V} :
    sharp x = 0 ↔ x = 0 := by
  refine ⟨fun hx => ?_, fun h => h.symm ▸ wittQuotientSharp_zero p d⟩
  have hreg : Function.Injective (fun x : U => (p : U) * x) :=
    wittQuotient_p_mul_injective_of_coeff_zero_regular p V d (mul_right_injective₀ ha)
  have hdiv (n : ℕ) (y : V) (hy : sharp y = 0) : y ∈ (Ideal.span {d₀}) ^ n := by
    induction n generalizing y with
    | zero => simp
    | succ n ih =>
      have hbar := wittQuotientSharp_modP p d y
      rw [hy, map_zero, map_zero] at hbar
      obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hbar.symm)
      obtain ⟨u, hu⟩ := wittQuotientSharp_associated_p p d hd
      have hmul : (p : U) * ((u : U) * sharp z) = (p : U) * 0 := by
        rw [mul_zero, ← mul_assoc, hu, ← map_mul, ← hz, hy]
      have hz0 : sharp z = 0 := u.isUnit.mul_left_cancel ((hreg hmul).trans (mul_zero _).symm)
      have hm := ih z hz0
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hm ⊢
      obtain ⟨c, hc⟩ := hm
      exact ⟨c, by rw [hz, hc, pow_succ]; ac_rfl⟩
  apply IsHausdorff.haus' (I := Ideal.span {d₀}) x
  intro n
  simpa [SModEq.sub_mem, Ideal.mul_top] using hdiv n x hx

private theorem wittQuotientSharp_associated_of_not_dvd_p
    (hd : (wittDeltaStructure p V).IsDistinguished d) (ha : ¬ IsUnit d₀)
    [IsAdicComplete (Ideal.span {(p : U)}) U] (x : U) (hx : ¬ (p : U) ∣ x) :
    ∃ b : V, Associated (sharp b) x := by
  let P := Ideal.span {(p : U)}
  let q := Ideal.Quotient.mk P
  let e := wittQuotientModPEquiv p V d
  have hproper : (Ideal.span {d₀} : Ideal V) ≠ ⊤ :=
    fun h => ha (Ideal.span_singleton_eq_top.mp h)
  let : Nontrivial (V ⧸ Ideal.span {d₀}) := (Ideal.Quotient.nontrivial_iff).mpr hproper
  let : Nontrivial (U ⧸ P) := e.symm.injective.nontrivial
  let : Nontrivial U := Ideal.Quotient.mk_surjective (I := P) |>.nontrivial
  let : IsLocalHom q := isLocalHom_mod_p_of_complete p
  let qV := Ideal.Quotient.mk (Ideal.span {d₀})
  let : IsLocalHom qV := IsLocalHom.of_surjective qV Ideal.Quotient.mk_surjective
  let : IsLocalRing (V ⧸ Ideal.span {d₀}) :=
    IsLocalRing.of_surjective qV Ideal.Quotient.mk_surjective
  let : IsLocalRing (U ⧸ P) := e.symm.isLocalRing
  have hlocal : IsLocalRing U := IsLocalRing.of_nonunits_add fun r s hr hs h =>
    (nonunits_add (fun h => hr (IsUnit.of_map q r h)) (fun h => hs (IsUnit.of_map q s h)))
      ((q.map_add r s) ▸ h.map q)
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (e (q x))
  have hb' : e (q (sharp b)) = e (q x) := (wittQuotientSharp_modP p d b).trans hb
  have hbnot : ¬ d₀ ∣ b := by
    intro h
    have hb0 : Ideal.Quotient.mk (Ideal.span {d₀}) b = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr h)
    have hx0 : q x = 0 := e.injective (hb.symm.trans (hb0.trans (map_zero e).symm))
    exact hx (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hx0))
  obtain ⟨r, hr⟩ := (ValuationRing.dvd_total b d₀).resolve_right hbnot
  have hru : ¬ IsUnit r := fun hu => hbnot (hr ▸ (associated_mul_unit_right _ _ hu).dvd')
  have hdif : x - sharp b ∈ P := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, (e.injective hb'), sub_self]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hdif
  obtain ⟨u, hu⟩ := (wittQuotientSharp_associated_p p d hd).symm
  have hrep : x = sharp b * (1 + sharp r * (u : U) * c) := by
    calc
      x = sharp b + (x - sharp b) := by ring
      _ = sharp b * (1 + sharp r * (u : U) * c) := by
        rw [hc, ← hu, hr, map_mul]
        ring
  have hnu : sharp r * (u : U) * c ∈ nonunits U :=
    fun h => hru ((wittQuotientSharp_isUnit_iff p d ha r).mp
      (isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left h)))
  have hunit : IsUnit (1 + sharp r * (u : U) * c) := by
    by_contra hn
    have hh := (maximalIdeal U).sub_mem ((mem_maximalIdeal _).mpr hn)
      ((mem_maximalIdeal _).mpr hnu)
    have h1 : (1 : U) ∈ maximalIdeal U := by simpa only [add_sub_cancel_right] using hh
    exact (maximalIdeal.isMaximal U).ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
  rw [hrep]
  exact ⟨b, associated_mul_unit_right _ _ hunit⟩

omit [IsDomain V] [ValuationRing V] in
private theorem wittQuotientCoeffZeroIdeal
    (hd : (wittDeltaStructure p V).IsDistinguished d) (h : d₀ = 0) :
    Ideal.span {d} = Ideal.span {(p : WittVector p V)} := by
  obtain ⟨u, hu⟩ := exists_teichmuller_add_p_mul_unit_of_distinguished p V d hd
  nth_rw 1 [hu]
  rw [h, WittVector.teichmuller_zero, zero_add]
  exact Ideal.span_singleton_mul_right_unit u.isUnit (p : WittVector p V)

private def wittQuotientCoeffZeroEquiv
    (hd : (wittDeltaStructure p V).IsDistinguished d) (h : d₀ = 0) : U ≃+* V :=
  (Ideal.quotEquivOfEq (wittQuotientCoeffZeroIdeal p d hd h)).trans WittVector.quotientPEquiv

omit [IsDomain V] [ValuationRing V] in
private theorem wittQuotientCoeffZeroEquiv_sharp
    (hd : (wittDeltaStructure p V).IsDistinguished d) (h : d₀ = 0) (x : V) :
    wittQuotientCoeffZeroEquiv p d hd h (sharp x) = x := by
  change WittVector.constantCoeff (WittVector.teichmuller p x) = x
  exact WittVector.teichmuller_coeff_zero p x

private theorem wittQuotientSharp_associated
    (hd : (wittDeltaStructure p V).IsDistinguished d) (ha : ¬ IsUnit d₀)
    [IsAdicComplete (Ideal.span {(p : U)}) U] (x : U) : ∃ b : V, Associated (sharp b) x := by
  classical
  by_cases hx : x = 0
  · exact ⟨0, by rw [hx, wittQuotientSharp_zero]⟩
  have hex : ∃ n : ℕ, ¬ (p : U) ^ n ∣ x := by
    by_contra! h
    apply hx
    apply IsHausdorff.haus' (I := Ideal.span {(p : U)}) x
    intro n
    simpa only [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] using h n
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero
    (show Nat.find hex ≠ 0 from fun h => Nat.find_spec hex (h ▸ by simp))
  have hn' : n < Nat.find hex := by omega
  have hdiv : (p : U) ^ n ∣ x := by simpa using Nat.find_min hex hn'
  obtain ⟨y, hy⟩ := hdiv
  have hy' : ¬ (p : U) ∣ y := by
    rintro ⟨z, hz⟩
    apply Nat.find_spec hex
    rw [hn]
    exact ⟨z, by rw [hy, hz, pow_succ, mul_assoc]⟩
  obtain ⟨b, hb⟩ := wittQuotientSharp_associated_of_not_dvd_p p d hd ha y hy'
  have hp := (wittQuotientSharp_associated_p p d hd).symm.pow_pow (n := n)
  refine ⟨d₀ ^ n * b, ?_⟩
  rw [map_mul, map_pow, hy]
  exact hp.mul_mul hb

private theorem wittQuotient_valuation_of_sharp (hV : ringKrullDim V = 1)
    (ha : ¬ IsUnit d₀) [IsAdicComplete (Ideal.span {(p : U)}) U]
    (hzero : ∀ x : V, sharp x = 0 ↔ x = 0)
    (hrep : ∀ x : U, ∃ b : V, Associated (sharp b) x) :
    IsRankOneCompleteValuationRing p U := by
  have hn : (1 : U) ≠ 0 := fun h => one_ne_zero ((hzero 1).mp ((map_one sharp).trans h))
  let : Nontrivial U := ⟨⟨1, 0, hn⟩⟩
  let : NoZeroDivisors U := ⟨fun {x y} hxy => by
    obtain ⟨r, hr⟩ := hrep x
    obtain ⟨s, hs⟩ := hrep y
    have h : sharp (r * s) = 0 := by
      rw [map_mul]
      exact (hr.mul_mul hs).eq_zero_iff.mpr hxy
    exact (mul_eq_zero.mp ((hzero _).mp h)).imp
      (fun h => hr.eq_zero_iff.mp ((hzero _).mpr h))
      (fun h => hs.eq_zero_iff.mp ((hzero _).mpr h))⟩
  let : IsDomain U := NoZeroDivisors.to_isDomain _
  let : ValuationRing U := ValuationRing.iff_dvd_total.mpr ⟨fun x y => by
    obtain ⟨r, hr⟩ := hrep x
    obtain ⟨s, hs⟩ := hrep y
    exact (ValuationRing.dvd_total r s).imp
      (fun h => hs.dvd_iff_dvd_right.mp (hr.dvd_iff_dvd_left.mp (map_dvd sharp h)))
      (fun h => hr.dvd_iff_dvd_right.mp (hs.dvd_iff_dvd_left.mp (map_dvd sharp h)))⟩
  refine ⟨inferInstance, inferInstance, ?_, inferInstance⟩
  apply ringKrullDim_eq_one_iff_of_isLocalRing_isDomain.mpr
  refine ⟨fun h => (ringKrullDim_eq_one_iff_of_isLocalRing_isDomain.mp hV).1 ?_, ?_⟩
  · refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, fun {x} hx => ?_⟩
    obtain ⟨b, hb⟩ := h.mul_inv_cancel (a := sharp x) (fun h => hx ((hzero x).mp h))
    have hu := (wittQuotientSharp_isUnit_iff p d ha x).mp (isUnit_iff_dvd_one.mpr ⟨b, hb.symm⟩)
    obtain ⟨z, hz⟩ := isUnit_iff_dvd_one.mp hu
    exact ⟨z, hz.symm⟩
  · intro x hx y hy
    obtain ⟨r, hr⟩ := hrep x
    obtain ⟨s, hs⟩ := hrep y
    have hr0 : r ≠ 0 := fun h => hx (hr.eq_zero_iff.mp ((hzero r).mpr h))
    have hsu : ¬ IsUnit s := fun h => (mem_maximalIdeal y).mp hy (hs.isUnit (h.map sharp))
    obtain ⟨n, hn⟩ := (ringKrullDim_eq_one_iff_of_isLocalRing_isDomain.mp hV).2 r hr0
      ((mem_maximalIdeal s).mpr hsu)
    have hd : r ∣ s ^ n := Ideal.mem_span_singleton.mp hn
    refine ⟨n, Ideal.mem_span_singleton.mpr ?_⟩
    apply hr.dvd_iff_dvd_left.mp
    apply (hs.pow_pow (n := n)).dvd_iff_dvd_right.mp
    simpa only [map_pow] using map_dvd sharp hd


omit [IsDomain V] [ValuationRing V] in
private theorem wittQuotient_p_nonunit (ha : ¬ IsUnit d₀) : ¬ IsUnit (p : U) := by
  let q := Ideal.Quotient.mk (Ideal.span {(p : U)})
  let e := wittQuotientModPEquiv p V d
  let : Nontrivial (V ⧸ Ideal.span {d₀}) := Ideal.Quotient.nontrivial_iff.mpr
    (fun h => ha (Ideal.span_singleton_eq_top.mp h))
  let : Nontrivial (U ⧸ Ideal.span {(p : U)}) := e.symm.injective.nontrivial
  intro hp
  have hz : q (p : U) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  exact not_isUnit_zero (hz ▸ hp.map q)

section

/-- a 進完備な階数 1 の完全付値環の distinguished Witt 商とその tilt。 -/
theorem untilt_rankOneValuationRing (V : Type u) [CommRing V] [IsDomain V] [ValuationRing V]
    [CharP V p] [PerfectRing V p] (hV : ringKrullDim V = 1)
    (d : WittVector p V) (hd : (wittDeltaStructure p V).IsDistinguished d)
    (ha : d.coeff 0 = 0 ∨ (d.coeff 0 ≠ 0 ∧ ¬ IsUnit (d.coeff 0)))
    (hc : IsAdicComplete (Ideal.span {d.coeff 0}) V) :
    let S := WittVector p V ⧸ Ideal.span {d}
    IsIntegralPerfectoid S p ∧ IsRankOneCompleteValuationRing p S ∧
      (∃ hpS : ¬ IsUnit (p : S),
        letI : Fact (¬ IsUnit (p : S)) := ⟨hpS⟩
        ∃ e : V ≃+* (tiltRing p S : Type u), e.toRingHom =
          (tiltRingEquivPreTilt p S).symm.toRingHom.comp (wittQuotientTiltMap p V d)) ∧
      (d.coeff 0 = 0 → Nonempty (S ≃+* V)) := by
  let S := WittVector p V ⧸ Ideal.span {d}
  let := hc
  let := (wittDeltaStructure_isPerfect p V).distinguished_quotient_isAdicComplete hd
  have hna : ¬ IsUnit (d.coeff 0) := ha.elim (fun h => h ▸ not_isUnit_zero) And.right
  have hp := wittQuotient_p_nonunit p d hna
  let : Fact (¬ IsUnit (p : S)) := ⟨hp⟩
  let z := wittQuotientSharp p d
  have hz (x : V) : z x = 0 ↔ x = 0 := by
    rcases ha with h | ⟨h, _⟩
    · refine ⟨fun hx => ?_, fun hx => hx.symm ▸ wittQuotientSharp_zero p d⟩
      let e := wittQuotientCoeffZeroEquiv p d hd h
      have he : e (z x) = x := wittQuotientCoeffZeroEquiv_sharp p d hd h x
      rw [hx, map_zero] at he
      exact he.symm
    · exact wittQuotientSharp_eq_zero_of_regular p d h hd
  have hrep (x : S) : ∃ b : V, Associated (z b) x :=
    wittQuotientSharp_associated p d hd hna x
  refine ⟨wittDistinguishedQuotient_isIntegralPerfectoid p V d hd,
    wittQuotient_valuation_of_sharp p d hV hna hz hrep, ?_,
    fun h => ⟨wittQuotientCoeffZeroEquiv p d hd h⟩⟩
  let L := wittQuotientTiltMap p V d
  have hL : Function.Injective L := (injective_iff_map_eq_zero L).mpr fun x hx => by
    apply (hz x).mp
    change L x = 0 at hx
    have he := wittQuotientTiltMap_untilt p V d x
    change (L x).untilt = z x at he
    have h0 : (0 : PreTilt S p).untilt = 0 := Perfection.teichmuller_zero
    rw [hx, h0] at he
    exact he.symm
  let e₀ := RingEquiv.ofBijective L ⟨hL, wittQuotientTiltMap_surjective p V d⟩
  exact ⟨hp, e₀.trans (tiltRingEquivPreTilt p S).symm, rfl⟩

end


end SerrePositivity.BhattScholze.Perfectoidization.Derived
