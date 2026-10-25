module

public import SerrePositivity.BhattScholze.Prism.Perfectoid.WittQuotientTiltEquiv
public import SerrePositivity.CommutativeAlgebra.WittLiftUniqueness
public import SerrePositivity.BhattScholze.Delta.Perfect.DistinguishedRegular

/-! # 完備distinguished Witt商への写像の忠実性

完全係数環からのWitt射は、商への射で決まる。
標準tilt比較射の単射性とPerfectionの普遍性を使う。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
variable (p : ℕ) [Fact p.Prime]
variable {k l : Type u} [CommRing k] [CharP k p] [PerfectRing k p]
variable [CommRing l] [CharP l p] [PerfectRing l p]

private def residueMap (f : WittVector p k →+* WittVector p l) : k →+* l :=
  (WittVector.constantCoeff : WittVector p k →+* k).liftOfSurjective
    (WittVector.constantCoeff_surjective p) ⟨WittVector.constantCoeff.comp f, by
      rw [WittVector.ker_constantCoeff, Ideal.span_singleton_le_iff_mem]
      change (f (p : WittVector p k)).coeff 0 = 0
      rw [map_natCast, WittVector.coeff_p_zero]⟩

omit [PerfectRing l p] in
private theorem residueMap_coeff (f : WittVector p k →+* WittVector p l) (x : WittVector p k) :
    residueMap p f (x.coeff 0) = (f x).coeff 0 :=
  RingHom.liftOfSurjective_comp_apply _ _ _ _

private theorem residueMap_wittMap (f : WittVector p k →+* WittVector p l) :
    f = WittVector.map (residueMap p f) := by
  apply wittLift_unique
  apply RingHom.ext
  intro x
  apply (WittVector.quotientPEquiv (p := p) (k := l)).injective
  change (f x).coeff 0 = (WittVector.map (residueMap p f) x).coeff 0
  rw [WittVector.map_coeff, residueMap_coeff]

/-- 完備distinguished Witt商への射が一致すれば、元のWitt環への射が一致する。 -/
theorem wittQuotientHom_ext (d : WittVector p l)
    [IsAdicComplete (Ideal.span {d}) (WittVector p l)]
    [Fact (¬ IsUnit (p : WittVector p l ⧸ Ideal.span {d}))]
    (hd : (wittDeltaStructure p l).IsDistinguished d)
    (f g : WittVector p k →+* WittVector p l)
    (h : (Ideal.Quotient.mk (Ideal.span {d})).comp f =
      (Ideal.Quotient.mk (Ideal.span {d})).comp g) : f = g := by
  let : IsAdicComplete (Ideal.span {(p : WittVector p l ⧸ Ideal.span {d})})
      (WittVector p l ⧸ Ideal.span {d}) :=
    (wittDeltaStructure_isPerfect p l).distinguished_quotient_isAdicComplete hd
  let L := wittQuotientTiltMap p l d
  have he : L.comp (residueMap p f) = L.comp (residueMap p g) := by
    apply Perfection.hom_ext
    intro x
    change PreTilt.coeff 0 (L (residueMap p f x)) =
      PreTilt.coeff 0 (L (residueMap p g x))
    rw [wittQuotientTiltMap_coeff, wittQuotientTiltMap_coeff]
    simp only [Function.iterate_zero, id_eq, wittQuotientCoefficientMap_apply]
    have hx := RingHom.congr_fun h (WittVector.teichmuller p x)
    rw [residueMap_wittMap p f, residueMap_wittMap p g] at hx
    simpa only [RingHom.comp_apply, WittVector.map_teichmuller] using
      congrArg (Ideal.Quotient.mk (Ideal.span {(p : WittVector p l ⧸ Ideal.span {d})})) hx
  have hres : residueMap p f = residueMap p g := by
    apply RingHom.ext
    intro x
    apply wittQuotientTiltMap_injective p l d hd
    exact RingHom.congr_fun he x
  rw [residueMap_wittMap p f, residueMap_wittMap p g, hres]

end SerrePositivity.BhattScholze
