module

public import SerrePositivity.BhattScholze.DeltaPerfectionUniversal
public import SerrePositivity.BhattScholze.PCompletedDeltaPerfection
public import SerrePositivity.BhattScholze.DeltaPDCompletionUniversal
public import SerrePositivity.BhattScholze.PDCompletionInterface
public import SerrePositivity.BhattScholze.PerfectDeltaFrobenius

/-! # 二つの実δ完全化PD完備化環の、同じ完全試験環への普遍性 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {B T : Type u} [CommRing B] [CommRing T]
variable (E : DeltaStructure p B) (b : B)
variable (F : DeltaStructure p T) (hF : F.IsPerfect) (f : B →+* T) (hf : E.IsDeltaHom F f)
variable (hp : IsModuleComplete T (p : T) (ModuleCat.of T T))
variable (hd : IsModuleComplete T (f b) (ModuleCat.of T T))
include hF hf hp hd

/-- δ完全化の直接PD完備化から、同じ完全なp,f(b)完備δ試験環への一意延長。 -/
theorem existsUnique_deltaPerfectionPDCompletionHom :
    letI := pdCompletionCommRing (DeltaPerfection E) p (deltaPerfectionOf E 0 b)
    ∃! g : PDCompletionH0 (DeltaPerfection E) p (deltaPerfectionOf E 0 b) →+* T,
      (deltaPDCompletionStructure (deltaPerfectionStructure E) (deltaPerfectionOf E 0 b)).IsDeltaHom
        F g ∧
      g.comp ((pdCompletionUnit (DeltaPerfection E) p (deltaPerfectionOf E 0 b)).comp
        (deltaPerfectionOf E 0)) = f := by
  let := pdCompletionCommRing (DeltaPerfection E) p (deltaPerfectionOf E 0 b)
  obtain ⟨k, hk, hku⟩ := existsUnique_deltaPerfectionHom E F hF f hf
  have hkb : k (deltaPerfectionOf E 0 b) = f b := RingHom.congr_fun hk.2 b
  have hdk : IsModuleComplete T (k (deltaPerfectionOf E 0 b)) (ModuleCat.of T T) := by
    rw [hkb]
    exact hd
  obtain ⟨g, hg, hgu⟩ := existsUnique_deltaPDCompletionHom
    (deltaPerfectionStructure E) (deltaPerfectionOf E 0 b) F k hk.1 hp hdk
  refine ⟨g, ⟨hg.1, ?_⟩, ?_⟩
  · rw [← RingHom.comp_assoc, hg.2, hk.2]
  · intro l hl
    have hlk : l.comp (pdCompletionUnit (DeltaPerfection E) p (deltaPerfectionOf E 0 b)) = k := by
      apply hku
      exact ⟨hl.1.comp (pdCompletionUnit_isDeltaHom _ _),
        by simpa only [RingHom.comp_assoc] using hl.2⟩
    exact hgu l ⟨hl.1, hlk⟩

/-- p完備化を先に施す既存候補も、同じ完全なp,f(b)完備δ試験環への普遍性を持つ。 -/
theorem existsUnique_pCompletedDeltaPerfectionPDCompletionHom :
    letI := pdCompletionCommRing (PCompletedDeltaPerfection E) p (pCompletedDeltaPerfectionMap E b)
    ∃! g : PDCompletionH0 (PCompletedDeltaPerfection E) p (pCompletedDeltaPerfectionMap E b) →+* T,
      (deltaPDCompletionStructure (pCompletedDeltaPerfectionStructure E)
        (pCompletedDeltaPerfectionMap E b)).IsDeltaHom F g ∧
      g.comp ((pdCompletionUnit (PCompletedDeltaPerfection E) p
        (pCompletedDeltaPerfectionMap E b)).comp (pCompletedDeltaPerfectionMap E)) = f := by
  let := pdCompletionCommRing (PCompletedDeltaPerfection E) p (pCompletedDeltaPerfectionMap E b)
  let : IsAdicComplete (Ideal.span {(p : T)}) T :=
    (isRingModuleComplete_iff_isAdicComplete_natCast T p hF.p_mul_injective).mp hp
  obtain ⟨k, hk, hku⟩ := existsUnique_pCompletedDeltaPerfectionHom E F hF f hf
  have hkb : k (pCompletedDeltaPerfectionMap E b) = f b := RingHom.congr_fun hk.2 b
  have hdk : IsModuleComplete T (k (pCompletedDeltaPerfectionMap E b)) (ModuleCat.of T T) := by
    rw [hkb]
    exact hd
  obtain ⟨g, hg, hgu⟩ := existsUnique_deltaPDCompletionHom
    (pCompletedDeltaPerfectionStructure E) (pCompletedDeltaPerfectionMap E b) F k hk.1 hp hdk
  refine ⟨g, ⟨hg.1, ?_⟩, ?_⟩
  · rw [← RingHom.comp_assoc, hg.2, hk.2]
  · intro l hl
    have hlk : l.comp
        (pdCompletionUnit (PCompletedDeltaPerfection E) p
          (pCompletedDeltaPerfectionMap E b)) = k := by
      apply hku
      exact ⟨hl.1.comp (pdCompletionUnit_isDeltaHom _ _),
        by simpa only [RingHom.comp_assoc] using hl.2⟩
    exact hgu l ⟨hl.1, hlk⟩

end SerrePositivity.BhattScholze
