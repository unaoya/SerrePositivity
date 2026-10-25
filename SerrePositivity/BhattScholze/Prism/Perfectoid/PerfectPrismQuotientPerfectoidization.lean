module

public import SerrePositivity.BhattScholze.Prism.Perfection.PerfectDeltaDivisionQuotient
public import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectPrismQuotientPerfectoid
public import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectPrismHomLift
public import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectoidTrialPrism

/-! # 完全prism商の任意の商の普遍perfectoid化

完全試験prismの普遍性を既存IsPerfectoidizationへ移す。
全射性は結論に含めない。実PD完備化を使い、古典的完備化への置換をしない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A S : Type u} [CommRing A] [CommRing S]

/-- 完全prism基底からの全射商の、具体的な除算prism商への標準射。 -/
def perfectPrismQuotientPerfectoidizationMap
    (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect)
    (r : A →+* S) (hr : Function.Surjective r) :
    letI := perfectDeltaDivisionPrismCommRing P.deltaStructure P.generator (RingHom.ker r)
    S →+* PerfectDeltaDivisionPrismCarrier P.deltaStructure P.generator (RingHom.ker r) ⧸
      (perfectDeltaDivisionPrism P.deltaStructure P.generator
        (P.isDistinguished_of_perfect hP) (RingHom.ker r)).ideal := by
  let := perfectDeltaDivisionPrismCommRing P.deltaStructure P.generator (RingHom.ker r)
  let j := perfectDeltaDivisionPrismMap P.deltaStructure P.generator (RingHom.ker r)
  let Q := perfectDeltaDivisionPrism P.deltaStructure P.generator
    (P.isDistinguished_of_perfect hP) (RingHom.ker r)
  exact r.liftOfSurjective hr ⟨(Ideal.Quotient.mk Q.ideal).comp j, by
    intro x hx
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact perfectDeltaDivisionPrismMap_ideal_le P.deltaStructure P.generator
      (P.isDistinguished_of_perfect hP) (RingHom.ker r) hx⟩

set_option maxHeartbeats 800000 in
-- 具体的な実完備化の環構造を展開するため、この証明に限って探索上限を増やす。
/-- 非零完全prismの商から来る全射について、具体的な標準射はperfectoid化を与える。 -/
theorem perfectPrismQuotientPerfectoidizationMap_isPerfectoidization
    (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect)
    [Fact (¬ IsUnit (p : A ⧸ P.ideal))]
    (r : A →+* S) (hr : Function.Surjective r) (hrd : r P.generator = 0) :
    letI := perfectDeltaDivisionPrismCommRing P.deltaStructure P.generator (RingHom.ker r)
    IsPerfectoidization p (perfectPrismQuotientPerfectoidizationMap P hP r hr) := by
  let D := P.deltaStructure
  let d := P.generator
  have hd := P.isDistinguished_of_perfect hP
  let J := RingHom.ker r
  let H := PerfectDeltaDivisionPrismCarrier D d J
  let := perfectDeltaDivisionPrismCommRing D d J
  let Q := perfectDeltaDivisionPrism D d hd J
  have hQ := perfectDeltaDivisionPrism_isPerfect D d hd J
  let j := perfectDeltaDivisionPrismMap D d J
  let C := H ⧸ Q.ideal
  let qC := Ideal.Quotient.mk Q.ideal
  have hjδ := perfectDeltaDivisionPrismMap_isDeltaHom D d hd J
  have hjI : P.ideal ≤ Q.ideal.comap j := by
    rw [OrientedPrism.ideal, Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_span_singleton_self _
  let base : OrientedPrism.Hom P Q := { j with map_delta := hjδ, ideal_le := hjI }
  let f : S →+* C := perfectPrismQuotientPerfectoidizationMap P hP r hr
  have hfr : f.comp r = qC.comp j := r.liftOfSurjective_comp hr _
  let s : A ⧸ P.ideal →+* S := Ideal.Quotient.lift _ r (by
    change P.ideal ≤ RingHom.ker r
    rw [OrientedPrism.ideal, Ideal.span_singleton_le_iff_mem]
    exact hrd)
  have hsr : s.comp (Ideal.Quotient.mk P.ideal) = r := rfl
  refine ⟨Q.quotient_isIntegralPerfectoid hQ, ?_⟩
  intro T _ hT g
  rcases hT with hs | ⟨hpT, hcT, ⟨π, u, hu⟩, hFT, hkerT⟩
  · let := hs
    let l : C →+* T :=
      { toFun := fun _ ↦ 0
        map_one' := Subsingleton.elim _ _
        map_mul' := fun _ _ ↦ Subsingleton.elim _ _
        map_zero' := rfl
        map_add' := fun _ _ ↦ Subsingleton.elim _ _ }
    refine ⟨l, ?_, ?_⟩
    · apply RingHom.ext
      intro x
      exact Subsingleton.elim _ _
    · intro k hk
      apply RingHom.ext
      intro x
      exact Subsingleton.elim _ _
  · let := hcT
    let : Fact (¬ IsUnit (p : T)) := ⟨hpT⟩
    obtain ⟨t, ht, et, het⟩ := exists_perfectoidTrialPrism T p hFT hkerT π u hu
    let := DerivedCompletion.pdCompletionCommRing (WittVector p (PreTilt T p)) p t
    let QT := perfectDeltaPDPrism (wittDeltaStructure p (PreTilt T p))
      (wittDeltaStructure_isPerfect p (PreTilt T p)) t ht
    have hQT := perfectDeltaPDPrism_isPerfect (wittDeltaStructure p (PreTilt T p))
      (wittDeltaStructure_isPerfect p (PreTilt T p)) t ht
    let : Fact (¬ IsUnit (p : _ ⧸ QT.ideal)) := ⟨fun h ↦ hpT
      (by simpa only [map_natCast] using h.map et.toRingHom)⟩
    let gP := et.symm.toRingHom.comp (g.comp s)
    obtain ⟨F, hF, hFu⟩ := existsUnique_perfectPrismHomLift P QT hP hQT gP
    have hFJ : J ≤ QT.ideal.comap F.toRingHom := by
      intro x hx
      change F.toRingHom x ∈ QT.ideal
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      have hh := RingHom.congr_fun hF (Ideal.Quotient.mk P.ideal x)
      change Ideal.Quotient.mk QT.ideal (F.toRingHom x) = et.symm (g (r x)) at hh
      rw [show r x = 0 from hx, map_zero, map_zero] at hh
      exact hh
    obtain ⟨K, hK, hKu⟩ := existsUnique_perfectDeltaDivisionPrismHom D d hd J QT hQT
      F.toRingHom F.map_delta F.map_generator_mem hFJ
    let l := et.toRingHom.comp K.quotientMap
    have hlg : l.comp f = g := by
      apply RingHom.ext
      intro x
      obtain ⟨a, rfl⟩ := hr x
      have hh : f (r a) = qC (j a) := RingHom.congr_fun hfr a
      change et (K.quotientMap (f (r a))) = g (r a)
      rw [hh, OrientedPrism.Hom.quotientMap_mk]
      have hk : K.toRingHom (j a) = F.toRingHom a := RingHom.congr_fun hK a
      rw [hk]
      have hff := RingHom.congr_fun hF (Ideal.Quotient.mk P.ideal a)
      change Ideal.Quotient.mk QT.ideal (F.toRingHom a) = et.symm (g (r a)) at hff
      rw [hff, et.apply_symm_apply]
    refine ⟨l, hlg, ?_⟩
    intro k hk
    rcases subsingleton_or_nontrivial C with hsub | hn
    · let := hsub
      apply RingHom.ext
      intro x
      rw [Subsingleton.elim x 0, map_zero, map_zero]
    · let := hn
      let : IsAdicComplete (Ideal.span {(p : C)}) C :=
        perfectDeltaDivisionQuotient_isAdicComplete D d hd J
      have hpC : ¬ IsUnit (p : C) := by
        intro h
        let : Subsingleton C := subsingleton_of_isUnit_natCast_of_isHausdorff p C h
        exact zero_ne_one (Subsingleton.elim (0 : C) 1)
      let : Fact (¬ IsUnit (p : C)) := ⟨hpC⟩
      obtain ⟨L, hL, _⟩ := existsUnique_perfectPrismHomLift Q QT hQ hQT
        (et.symm.toRingHom.comp k)
      have hLF : L.comp base = F := by
        apply hFu
        apply Ideal.Quotient.ringHom_ext
        apply RingHom.ext
        intro a
        change Ideal.Quotient.mk QT.ideal (L.toRingHom (j a)) = et.symm (g (r a))
        have hll := RingHom.congr_fun hL (qC (j a))
        change Ideal.Quotient.mk QT.ideal (L.toRingHom (j a)) = et.symm (k (qC (j a))) at hll
        rw [hll]
        have hh : f (r a) = qC (j a) := RingHom.congr_fun hfr a
        rw [← hh]
        have hkg : k (f (r a)) = g (r a) := RingHom.congr_fun hk (r a)
        rw [hkg]
      have hLK : L = K := hKu L (congrArg OrientedPrism.Hom.toRingHom hLF)
      apply RingHom.ext
      intro x
      have hh := RingHom.congr_fun hL x
      change L.quotientMap x = et.symm (k x) at hh
      rw [hLK] at hh
      change k x = et (K.quotientMap x)
      rw [hh, et.apply_symm_apply]

/-- 完全prismの商の任意の全射商には、環として普遍なperfectoid化が存在する。 -/
theorem exists_perfectoidization_of_perfectPrism_quotient
    (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect)
    [Fact (¬ IsUnit (p : A ⧸ P.ideal))]
    (r : A →+* S) (hr : Function.Surjective r) (hrd : r P.generator = 0) :
    ∃ (C : Type u) (_ : CommRing C) (f : S →+* C), IsPerfectoidization p f := by
  let := perfectDeltaDivisionPrismCommRing P.deltaStructure P.generator (RingHom.ker r)
  exact ⟨_, inferInstance, perfectPrismQuotientPerfectoidizationMap P hP r hr,
    perfectPrismQuotientPerfectoidizationMap_isPerfectoidization P hP r hr hrd⟩

end SerrePositivity.BhattScholze
