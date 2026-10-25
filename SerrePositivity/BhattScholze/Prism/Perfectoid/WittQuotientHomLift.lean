module

public import SerrePositivity.BhattScholze.Prism.Perfectoid.WittQuotientHomFaithful
public import SerrePositivity.BhattScholze.Prism.Perfectoid.WittCompleteQuotientPerfectoid
public import SerrePositivity.BhattScholze.Prism.Perfectoid.FontaineNaturality

/-! # 一般の完備distinguished Witt商の射の唯一持上げ -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable (p : ℕ) [Fact p.Prime]
variable {k l : Type u} [CommRing k] [CharP k p] [PerfectRing k p]
variable [CommRing l] [CharP l p] [PerfectRing l p]

/-- 完備distinguished Witt商間の環射は、唯一の標準δ射に持ち上がる。 -/
theorem existsUnique_wittQuotientHomLift (d : WittVector p k) (e : WittVector p l)
    [IsAdicComplete (Ideal.span {d}) (WittVector p k)]
    [IsAdicComplete (Ideal.span {e}) (WittVector p l)]
    [Fact (¬ IsUnit (p : WittVector p k ⧸ Ideal.span {d}))]
    [Fact (¬ IsUnit (p : WittVector p l ⧸ Ideal.span {e}))]
    (hd : (wittDeltaStructure p k).IsDistinguished d)
    (he : (wittDeltaStructure p l).IsDistinguished e)
    (g : WittVector p k ⧸ Ideal.span {d} →+* WittVector p l ⧸ Ideal.span {e}) :
    ∃! f : WittVector p k →+* WittVector p l,
      (wittDeltaStructure p k).IsDeltaHom (wittDeltaStructure p l) f ∧
      (Ideal.Quotient.mk (Ideal.span {e})).comp f =
        g.comp (Ideal.Quotient.mk (Ideal.span {d})) := by
  let S := WittVector p k ⧸ Ideal.span {d}
  let T := WittVector p l ⧸ Ideal.span {e}
  let : IsAdicComplete (Ideal.span {(p : S)}) S :=
    (wittDeltaStructure_isPerfect p k).distinguished_quotient_isAdicComplete hd
  let : IsAdicComplete (Ideal.span {(p : T)}) T :=
    (wittDeltaStructure_isPerfect p l).distinguished_quotient_isAdicComplete he
  let es := RingEquiv.ofBijective (wittQuotientFontaineMap p k d)
    (wittCompleteQuotientFontaineMap_bijective p k d hd)
  let et := RingEquiv.ofBijective (wittQuotientFontaineMap p l e)
    (wittCompleteQuotientFontaineMap_bijective p l e he)
  let m : WittVector p (PreTilt S p) →+* WittVector p (PreTilt T p) :=
    WittVector.map (Perfection.map p (modPMap p g))
  let f := et.symm.toRingHom.comp (m.comp es.toRingHom)
  have het : (Ideal.Quotient.mk (Ideal.span {e})).comp et.symm.toRingHom =
      WittVector.fontaineTheta T p := by
    apply RingHom.ext
    intro x
    obtain ⟨y, rfl⟩ := et.surjective x
    change Ideal.Quotient.mk _ (et.symm (et y)) = WittVector.fontaineTheta T p (et y)
    rw [et.symm_apply_apply]
    exact (RingHom.congr_fun (wittQuotientFontaineMap_comp_fontaineTheta p l e) y).symm
  have hfg : (Ideal.Quotient.mk (Ideal.span {e})).comp f =
      g.comp (Ideal.Quotient.mk (Ideal.span {d})) := by
    change (Ideal.Quotient.mk _).comp (et.symm.toRingHom.comp (m.comp es.toRingHom)) = _
    rw [← RingHom.comp_assoc, het, ← RingHom.comp_assoc,
      fontaineTheta_natural p g, RingHom.comp_assoc]
    change g.comp ((WittVector.fontaineTheta S p).comp (wittQuotientFontaineMap p k d)) = _
    rw [wittQuotientFontaineMap_comp_fontaineTheta]
  refine ⟨f, ⟨?_, hfg⟩, ?_⟩
  · exact ((wittQuotientFontaineMap_isDeltaHom p l e).symm).comp
      ((wittDeltaStructure_map_isDeltaHom p (PreTilt S p)
        (Perfection.map p (modPMap p g))).comp (wittQuotientFontaineMap_isDeltaHom p k d))
  · intro h hh
    exact wittQuotientHom_ext p e he h f (hh.2.trans hfg.symm)

end SerrePositivity.BhattScholze
