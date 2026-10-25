module

public import SerrePositivity.BhattScholze.RootedExtension.DeltaPerfectionPDCompletionUniversal

/-! # PD完備化を先に挟んだδ完全化の同じ試験環への普遍性 -/

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
local notation "S" => PDCompletionH0 B p b
local notation "G" => deltaPDCompletionStructure E b
local notation "v" => pdCompletionUnit B p b
local notation "C" => DeltaPerfection G
local notation "x" => deltaPerfectionOf G 0 (v b)
local notation "r" => RingHom.comp (pdCompletionUnit C p x) (deltaPerfectionOf G 0)
include hF hf hp hd

/-- 実PD完備化を先に挟んでも、元Bから同じ完全p,f(b)完備δ試験環への一意延長を得る。 -/
theorem existsUnique_deltaPDCompletionPerfectionPDHom :
    letI := pdCompletionCommRing B p b
    letI := pdCompletionCommRing C p x
    ∃! g : PDCompletionH0 C p x →+* T,
      (deltaPDCompletionStructure (deltaPerfectionStructure G) x).IsDeltaHom F g ∧
        g.comp ((r).comp v) = f := by
  let := pdCompletionCommRing B p b
  let := pdCompletionCommRing C p x
  obtain ⟨k, hk, hku⟩ := existsUnique_deltaPDCompletionHom E b F f hf hp hd
  have hkb : k (v b) = f b := RingHom.congr_fun hk.2 b
  have hdk : IsModuleComplete T (k (v b)) (ModuleCat.of T T) := by
    rw [hkb]
    exact hd
  obtain ⟨g, hg, hgu⟩ := existsUnique_deltaPerfectionPDCompletionHom G (v b) F hF k hk.1 hp hdk
  refine ⟨g, ⟨hg.1, ?_⟩, ?_⟩
  · rw [← RingHom.comp_assoc, hg.2, hk.2]
  · intro l hl
    have hlk : l.comp r = k := by
      apply hku
      refine ⟨hl.1.comp ?_, ?_⟩
      · exact (pdCompletionUnit_isDeltaHom _ _).comp (deltaPerfectionOf_isDeltaHom G 0)
      · simpa only [RingHom.comp_assoc] using hl.2
    exact hgu l ⟨hl.1, hlk⟩

end SerrePositivity.BhattScholze
