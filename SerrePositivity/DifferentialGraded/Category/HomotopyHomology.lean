module
public import SerrePositivity.DifferentialGraded.Category.Homotopy
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # dg圏のH⁰の射と主Hom複体の次数零ホモロジー -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
variable (x y : ClosedCategory A D)

def homotopyHomFromCycle (c : zeroCycles (homObject A D x y)) :
    (toHomotopy A D).obj x ⟶ (toHomotopy A D).obj y :=
  (toHomotopy A D).map ((closedHomEquiv A D x y).symm c)

lemma homotopyHomFromCycle_surjective : Function.Surjective (homotopyHomFromCycle A D x y) := by
  intro f
  obtain ⟨g, rfl⟩ := (toHomotopy A D).map_surjective f
  exact ⟨closedHomEquiv A D x y g,
    congrArg ((toHomotopy A D).map) ((closedHomEquiv A D x y).symm_apply_apply g)⟩

lemma homotopyHomFromCycle_eq_iff (c d : zeroCycles (homObject A D x y)) :
    homotopyHomFromCycle A D x y c = homotopyHomFromCycle A D x y d ↔
      c - d ∈ LinearMap.range ((homObject A D x y).sc' (-1) 0 1).moduleCatToCycles := by
  rw [homotopyHomFromCycle, homotopyHomFromCycle, toHomotopy_map_eq_iff_boundary]
  change (∃ h, (homObject A D x y).d (-1) 0 h =
    (cycleFromUnit _ (unitFromCycle _ c)).val -
      (cycleFromUnit _ (unitFromCycle _ d)).val) ↔ _
  rw [cycleFromUnit_unitFromCycle, cycleFromUnit_unitFromCycle]
  constructor
  · rintro ⟨h, hh⟩
    exact ⟨h, Subtype.ext hh⟩
  · rintro ⟨h, hh⟩
    exact ⟨h, congrArg Subtype.val hh⟩

/-- 具体的なcycle/boundary商からH⁰の実際の射への写像。 -/
def homotopyHomFromCohomologyQuotient :
    ((homObject A D x y).sc' (-1) 0 1).moduleCatLeftHomologyData.H →
      ((toHomotopy A D).obj x ⟶ (toHomotopy A D).obj y) :=
  Quotient.lift (homotopyHomFromCycle A D x y) (fun c d h =>
    (homotopyHomFromCycle_eq_iff A D x y c d).2 ((Submodule.quotientRel_def _).mp h))

lemma homotopyHomFromCohomologyQuotient_bijective :
    Function.Bijective (homotopyHomFromCohomologyQuotient A D x y) := by
  constructor
  · intro c d
    induction c using Quotient.inductionOn with | _ c =>
      induction d using Quotient.inductionOn with | _ d =>
        intro h
        exact Quotient.sound ((Submodule.quotientRel_def _).mpr
          ((homotopyHomFromCycle_eq_iff A D x y c d).1 h))
  · intro f
    obtain ⟨c, hc⟩ := homotopyHomFromCycle_surjective A D x y f
    exact ⟨Submodule.Quotient.mk c, hc⟩

/-- cycle/boundary商とMathlibの次数零ホモロジーの標準比較。 -/
def complexZeroHomologyQuotientIso (K : Complex A) :
    (K.sc' (-1) 0 1).moduleCatLeftHomologyData.H ≅ K.homology 0 :=
  (K.sc' (-1) 0 1).moduleCatHomologyIso.symm ≪≫
    (K.homologyIsoSc' (-1) 0 1 (by simp) (by simp)).symm

def complexZeroHomologyClass (K : Complex A) (c : zeroCycles K) : K.homology 0 :=
  (complexZeroHomologyQuotientIso A K).hom (Submodule.Quotient.mk c)

/-- 対象のHom複体の実際のMathlib homologyを用いるH⁰の射計算。 -/
def homotopyHomologyEquiv :
    ((toHomotopy A D).obj x ⟶ (toHomotopy A D).obj y) ≃
      (homObject A D x y).homology 0 :=
  (Equiv.ofBijective _ (homotopyHomFromCohomologyQuotient_bijective A D x y)).symm.trans
    (complexZeroHomologyQuotientIso A (homObject A D x y)).toLinearEquiv.toEquiv

lemma homotopyHomologyEquiv_cycle (c : zeroCycles (homObject A D x y)) :
    homotopyHomologyEquiv A D x y (homotopyHomFromCycle A D x y c) =
      complexZeroHomologyClass A (homObject A D x y) c := by
  change (complexZeroHomologyQuotientIso A (homObject A D x y)).hom
    ((Equiv.ofBijective _ (homotopyHomFromCohomologyQuotient_bijective A D x y)).symm
      ((Equiv.ofBijective _ (homotopyHomFromCohomologyQuotient_bijective A D x y))
        (Submodule.Quotient.mk c))) = _
  rw [Equiv.symm_apply_apply]
  rfl

lemma homotopyHomologyEquiv_map (f : x ⟶ y) :
    homotopyHomologyEquiv A D x y ((toHomotopy A D).map f) =
      complexZeroHomologyClass A (homObject A D x y) (closedHomEquiv A D x y f) := by
  simpa only [homotopyHomFromCycle, Equiv.symm_apply_apply] using
    homotopyHomologyEquiv_cycle A D x y (closedHomEquiv A D x y f)

end SerrePositivity.DifferentialGraded
