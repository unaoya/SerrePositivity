module

public import SerrePositivity.BhattScholze.PerfectPrismQuotientPerfectoidization

/-! # B3：perfectoid環の商の普遍perfectoid化

著者公開版Corollary 7.3の存在・普遍性。
δ除算→完全化→実PD完備化の完全試験prismへの普遍性とTheorem 3.10の対応を合成する。
商の導来p完備性を課した原典入力を公開し、より一般の全射商の入口も分ける。
全射性・B-I・Andréの引用を使わない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R S : Type u} [CommRing R] [CommRing S]

/-- 任意のperfectoid環の全射商には、環として普遍なperfectoid化が存在する。
導来完備化を構成に組み込むため、源の商の完備性はこの強い入口には不要。 -/
theorem exists_perfectoidization_of_perfectoid_surjective_quotient
    (hR : IsIntegralPerfectoid R p) (q : R →+* S) (hq : Function.Surjective q) :
    ∃ (C : Type u) (_ : CommRing C) (f : S →+* C), IsPerfectoidization p f := by
  rcases hR with hs | ⟨hp, hc, ⟨π, u, hu⟩, hF, hker⟩
  · let := hs
    let : Subsingleton S := q.codomain_trivial
    refine ⟨S, inferInstance, RingHom.id S, Or.inl inferInstance, ?_⟩
    intro T _ hT g
    refine ⟨g, RingHom.comp_id _, ?_⟩
    intro l hl
    simpa only [RingHom.comp_id] using hl
  · let := hc
    let : Fact (¬ IsUnit (p : R)) := ⟨hp⟩
    obtain ⟨d, hd, e, he⟩ := exists_perfectoidTrialPrism R p hF hker π u hu
    let := DerivedCompletion.pdCompletionCommRing (WittVector p (PreTilt R p)) p d
    let P := perfectDeltaPDPrism (wittDeltaStructure p (PreTilt R p))
      (wittDeltaStructure_isPerfect p (PreTilt R p)) d hd
    have hP := perfectDeltaPDPrism_isPerfect (wittDeltaStructure p (PreTilt R p))
      (wittDeltaStructure_isPerfect p (PreTilt R p)) d hd
    let : Fact (¬ IsUnit (p : _ ⧸ P.ideal)) := ⟨fun h ↦ hp
      (by simpa only [map_natCast] using h.map e.toRingHom)⟩
    let r := q.comp (e.toRingHom.comp (Ideal.Quotient.mk P.ideal))
    have hr : Function.Surjective r := hq.comp (e.surjective.comp Ideal.Quotient.mk_surjective)
    have hrd : r P.generator = 0 := by
      change q (e (Ideal.Quotient.mk P.ideal P.generator)) = 0
      have hz : Ideal.Quotient.mk P.ideal P.generator = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
      rw [hz, map_zero, map_zero]
    exact exists_perfectoidization_of_perfectPrism_quotient P hP r hr hrd

/-- B3の原典入力：任意perfectoid環の導来p完備な全射商の存在と普遍性。
一般のpねじれ商を含む。全射性は別のB4工程。 -/
theorem exists_perfectoidization_of_semiperfectoid_quotient
    (hR : IsIntegralPerfectoid R p) (q : R →+* S) (hq : Function.Surjective q)
    (_hS : DerivedCompletion.IsModuleComplete S (p : S) (ModuleCat.of S S)) :
    ∃ (C : Type u) (_ : CommRing C) (f : S →+* C), IsPerfectoidization p f :=
  exists_perfectoidization_of_perfectoid_surjective_quotient hR q hq

end SerrePositivity.BhattScholze
