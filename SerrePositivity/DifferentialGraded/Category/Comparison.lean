module
public import SerrePositivity.DifferentialGraded.Category.Examples
public import SerrePositivity.DifferentialGraded.Category.Homotopy

/-! # Ch(A) の境界商と既存の chain homotopy の比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CochainComplex HomComplex
variable (A : Type u) [CommRing A]

/-- Ch(A) の dg 境界関係は、既存 chain map の通常のホモトピー関係に一致する。 -/
lemma complex_boundary_iff (X Y : Complex A)
    (f g : ForgetEnrichment.of (Complex A) X ⟶ ForgetEnrichment.of (Complex A) Y) :
    boundaryRelation A (Complex A) f g ↔
      Nonempty (Homotopy (complexClosedHomEquiv A X Y f) (complexClosedHomEquiv A X Y g)) := by
  rw [boundaryRelation, unit_homotopy_boundary]
  constructor
  · rintro ⟨h, dh⟩
    apply Nonempty.intro
    refine (Cochain.equivHomotopy _ _).symm ⟨h, ?_⟩
    rw [complexClosedHomEquiv_cochain, complexClosedHomEquiv_cochain]
    change _ = (homComplex A X Y).d (-1) 0 h + _
    change (homComplex A X Y).d (-1) 0 h =
      (cycleFromUnit (homComplex A X Y) f).val -
        (cycleFromUnit (homComplex A X Y) g).val at dh
    rw [dh]
    abel
  · rintro ⟨h⟩
    refine ⟨Cochain.ofHomotopy h, ?_⟩
    change δ (-1) 0 (Cochain.ofHomotopy h) = _
    rw [δ_ofHomotopy, complexClosedHomEquiv_cochain, complexClosedHomEquiv_cochain]
    rfl

/-- H⁰(Ch(A)) での等式は既存の chain homotopy と同値。 -/
lemma complex_H0_eq_iff (X Y : Complex A)
    (f g : ForgetEnrichment.of (Complex A) X ⟶ ForgetEnrichment.of (Complex A) Y) :
    (toHomotopy A (Complex A)).map f = (toHomotopy A (Complex A)).map g ↔
      Nonempty (Homotopy (complexClosedHomEquiv A X Y f) (complexClosedHomEquiv A X Y g)) := by
  rw [toHomotopy_map_eq_iff, complex_boundary_iff]
end SerrePositivity.DifferentialGraded
