module

public import SerrePositivity.CommutativeAlgebra.AdicKernelQuotient
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.AdicCompletion.Topology

/-! # Completeness of the image of a map to a separated ring -/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity

/-- The image of a p-adically complete ring in a p-adically separated ring is
p-adically complete, without a finite generation assumption on the kernel. -/
theorem isAdicComplete_ringHom_range {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (p : ℕ) (f : R →+* S)
    [IsAdicComplete (Ideal.span {(p : R)}) R]
    [IsHausdorff (Ideal.span {(p : S)}) S] :
    IsAdicComplete (Ideal.span {(p : f.range)}) f.range := by
  let : Algebra R S := f.toAlgebra
  have hmap : (Ideal.span {(p : R)}).map (algebraMap R S) =
      Ideal.span {(p : S)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  let : IsHausdorff (Ideal.span {(p : R)}) S := by
    exact (IsHausdorff.map_algebraMap_iff (I := Ideal.span {(p : R)}) (S := S) (M := S)).mp
      (by simpa only [hmap] using (inferInstance : IsHausdorff (Ideal.span {(p : S)}) S))
  let : IsAdicComplete (Ideal.span {(p : R)}) (R ⧸ RingHom.ker f) :=
    isAdicComplete_quotient_ker (Ideal.span {(p : R)}) (Algebra.linearMap R S)
  have hQmap : (Ideal.span {(p : R)}).map (algebraMap R (R ⧸ RingHom.ker f)) =
      Ideal.span {(p : R ⧸ RingHom.ker f)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have hQ : IsAdicComplete (Ideal.span {(p : R ⧸ RingHom.ker f)})
      (R ⧸ RingHom.ker f) := by
    rw [← hQmap]
    exact (IsAdicComplete.map_algebraMap_iff _ _).mpr inferInstance
  let e := RingHom.quotientKerEquivRange f
  have he := (IsAdicComplete.congr_ringEquiv
    (Ideal.span {(p : R ⧸ RingHom.ker f)}) e).mpr hQ
  simpa only [Ideal.map_span, Set.image_singleton, map_natCast] using he

end SerrePositivity
