module

public import SerrePositivity.AlgebraicGeometry.OpenIsomorphismBaseChange
public import SerrePositivity.AlgebraicGeometry.BlowupAway
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
概要：中心外の素点で局所化すると、中心の補開集合の逆像が全空間になる。
方針：中心に属して素点に属さない元は局所化後に単元になる。
規約：局所化は元の素イデアルの補集合に沿うもの。
使われ方：中心外で同型な射の素点ごとの底変換を同型にする。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u
variable {R : Type u} [CommRing R]

/-- 中心外の素点で局所化すると、中心の補開集合の逆像は全空間。 -/
theorem affineCenterComplement_localization_preimage_top (I : Ideal R) (P : PrimeSpectrum R)
    (hP : P ∉ PrimeSpectrum.zeroLocus (I : Set R)) :
    Spec.map (CommRingCat.ofHom (algebraMap R (Localization P.asIdeal.primeCompl))) ⁻¹ᵁ
      affineCenterComplement I = ⊤ := by
  apply top_le_iff.mp
  intro Q _
  apply (mem_affineCenterComplement I _).mpr
  intro hI
  have hn : ¬ (I : Set R) ⊆ P.asIdeal := hP
  obtain ⟨a, haI, haP⟩ := Set.not_subset.mp hn
  have hu : IsUnit (algebraMap R (Localization P.asIdeal.primeCompl) a) :=
    IsLocalization.map_units (Localization P.asIdeal.primeCompl) (⟨a, haP⟩ : P.asIdeal.primeCompl)
  exact Ideal.notMem_of_isUnit Q.asIdeal hu (hI haI)

/-- 中心外で同型な射は、中心外の素点での局所化後にも同型。 -/
theorem pullback_localization_isIso_of_centerComplement
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (I : Ideal R)
    [IsIso (f ∣_ affineCenterComplement I)] (P : PrimeSpectrum R)
    (hP : P ∉ PrimeSpectrum.zeroLocus (I : Set R)) :
    IsIso (pullback.snd f (Spec.map
      (CommRingCat.ofHom (algebraMap R (Localization P.asIdeal.primeCompl))))) :=
  pullback_snd_isIso_of_open_preimage_top f _ (affineCenterComplement I)
    (affineCenterComplement_localization_preimage_top I P hP)

end SerrePositivity.AlgebraicGeometry
