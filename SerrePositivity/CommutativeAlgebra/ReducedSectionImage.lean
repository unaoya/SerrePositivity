module

public import Mathlib.AlgebraicGeometry.StructureSheaf
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # 被約アフィン環の開集合上の切断への写像の核

開集合上で零となる元は、その開集合の全ての点で消える元と一致する。
開集合の準コンパクト性や環の Noether 性は不要。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
open TopologicalSpace Opposite
open AlgebraicGeometry

/-- 被約環では、構造層の開集合上の切断への写像の核はその開集合の消滅イデアルである。 -/
theorem ker_algebraMap_sections_eq_vanishingIdeal
    (R : Type u) [CommRing R] [IsReduced R] (U : Opens (PrimeSpectrum R)) :
    RingHom.ker (algebraMap R ((Spec.structureSheaf R).obj.obj (op U))) =
      PrimeSpectrum.vanishingIdeal (U : Set (PrimeSpectrum R)) := by
  ext f
  change algebraMap R ((Spec.structureSheaf R).obj.obj (op U)) f = 0 ↔ _
  rw [PrimeSpectrum.mem_vanishingIdeal]
  constructor
  · intro h x hx
    have hz := congrArg (fun s => s.1 ⟨x, hx⟩) h
    change LocalizedModule.mkLinearMap x.asIdeal.primeCompl R f = 0 at hz
    obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff x.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap x.asIdeal.primeCompl R)).mp hz
    have hsf : (s : R) * f = 0 := hs
    exact (x.2.mem_or_mem (hsf ▸ x.asIdeal.zero_mem)).resolve_left s.property
  · intro h
    apply Subtype.ext
    funext x
    change LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl R f = 0
    obtain ⟨_, ⟨_, ⟨b, rfl⟩, rfl⟩, hbx, hbU⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open x.2 U.2
    have hnil : IsNilpotent (b * f) := by
      apply (PrimeSpectrum.basicOpen_eq_bot_iff _).mp
      apply le_antisymm ?_ bot_le
      intro y hy
      rw [PrimeSpectrum.basicOpen_mul] at hy
      exact False.elim (hy.2 (h y (hbU hy.1)))
    apply (IsLocalizedModule.eq_zero_iff x.1.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl R)).mpr
    refine ⟨⟨b, hbx⟩, ?_⟩
    exact IsReduced.eq_zero (b * f) hnil

/-- Spec R の開集合の閉包は、元の切断写像の核の零点集合である。 -/
theorem zeroLocus_ker_algebraMap_sections
    (R : Type u) [CommRing R] [IsReduced R] (U : Opens (PrimeSpectrum R)) :
    PrimeSpectrum.zeroLocus
      (RingHom.ker (algebraMap R ((Spec.structureSheaf R).obj.obj (op U))) : Set R) =
      closure (U : Set (PrimeSpectrum R)) := by
  rw [ker_algebraMap_sections_eq_vanishingIdeal, PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]

end SerrePositivity
