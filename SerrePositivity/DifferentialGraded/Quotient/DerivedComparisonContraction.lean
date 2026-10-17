module
public import SerrePositivity.DifferentialGraded.Quotient.EpsilonContraction
public import SerrePositivity.DifferentialGraded.Module.YonedaFunctor
public import SerrePositivity.DifferentialGraded.Perfect.UniversalProperty

/-! # 明示的 dg 商が殺す代表対象

指定 ε の境界式を既存 H⁰ 商へ渡し、dg Yoneda と主導来局所化で零性を運ぶ。
この段階には局所 K-flat 仮定を用いない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 単位が境界である対象は、既存の H⁰ で零対象になる。 -/
lemma homotopy_isZero_of_unit_boundary (x : D)
    (h : (homObject A D x x).X (-1))
    (dh : (homObject A D x x).d (-1) 0 h = (unitElement A x).val) :
    IsZero ((toHomotopy A D).obj (ForgetEnrichment.of (Complex A) x)) := by
  apply (IsZero.iff_id_eq_zero _).2
  rw [← CategoryTheory.Functor.map_id, ← CategoryTheory.Functor.map_zero]
  apply (toHomotopy_map_eq_iff_boundary A D _ _).2
  refine ⟨h, ?_⟩
  change (homObject A D x x).d (-1) 0 h = (unitElement A x).val - 0
  simpa only [sub_zero] using dh

variable [Small.{u} D]

instance quotientObjectSmall (S : Set D) : Small.{u} (QuotientObject D S) :=
  small_of_injective (f := fun x : QuotientObject D S => x.val)
    (fun ⟨x⟩ ⟨y⟩ h => by cases h; rfl)

lemma quotientObject_homotopy_isZero (S : Set D) (b : S) :
    IsZero ((toHomotopy A (QuotientObject D S)).obj
      (ForgetEnrichment.of (Complex A) (⟨b.val⟩ : QuotientObject D S))) :=
  homotopy_isZero_of_unit_boundary A (QuotientObject D S) ⟨b.val⟩
    (epsilonElement A D S b) (differential_epsilonElement A D S b)

/-- 零になる対象の代表加群も、主導来圏で零になる。 -/
lemma representable_derived_isZero_of_unit_boundary (x : D)
    (h : (homObject A D x x).X (-1))
    (dh : (homObject A D x x).d (-1) 0 h = (unitElement A x).val) :
    IsZero ((moduleToDerived A D).obj
      (ForgetEnrichment.of (Complex A) (representable A x))) := by
  have hx := homotopy_isZero_of_unit_boundary A D x h dh
  have hR := (dgYoneda A D).onHomotopy.map_isZero hx
  have hQ := (moduleHomotopyToDerivedClosed A D).map_isZero hR
  exact hQ.of_iso ((moduleToHomotopyDerivedIso A D).app
    (ForgetEnrichment.of (Complex A) (representable A x))).symm

/-- S の代表加群は、明示的商の主導来圏で零。 -/
lemma quotientRepresentable_derived_isZero (S : Set D) (b : S) :
    IsZero ((moduleToDerived A (QuotientObject D S)).obj
      (ForgetEnrichment.of (Complex A) (representable A (⟨b.val⟩ : QuotientObject D S)))) :=
  representable_derived_isZero_of_unit_boundary A (QuotientObject D S) ⟨b.val⟩
    (epsilonElement A D S b) (differential_epsilonElement A D S b)

end SerrePositivity.DifferentialGraded.DGQuotient
