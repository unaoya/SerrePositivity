module
public import SerrePositivity.DifferentialGraded.Category.HomotopyHomology

/-! # H⁰の射と主Homのホモロジーの線形比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A]

lemma complexZeroHomologyClass_add (K : Complex A) (c d : zeroCycles K) :
    complexZeroHomologyClass A K (c + d) =
      complexZeroHomologyClass A K c + complexZeroHomologyClass A K d := by
  exact map_add (complexZeroHomologyQuotientIso A K).hom.hom
    (Submodule.Quotient.mk c) (Submodule.Quotient.mk d)

lemma complexZeroHomologyClass_smul (K : Complex A) (a : A) (c : zeroCycles K) :
    complexZeroHomologyClass A K (a • c) = a • complexZeroHomologyClass A K c := by
  exact map_smul (complexZeroHomologyQuotientIso A K).hom.hom a (Submodule.Quotient.mk c)

variable (D : Type v) [DGCategory A D] (x y : ClosedCategory A D)

lemma closedHomEquiv_add (f g : x ⟶ y) :
    closedHomEquiv A D x y (f + g) = closedHomEquiv A D x y f + closedHomEquiv A D x y g := by
  apply Subtype.ext
  rfl

lemma closedHomEquiv_smul (a : A) (f : x ⟶ y) :
    closedHomEquiv A D x y (a • f) = a • closedHomEquiv A D x y f := by
  apply Subtype.ext
  rfl

lemma homotopyHomologyEquiv_add
    (f g : (toHomotopy A D).obj x ⟶ (toHomotopy A D).obj y) :
    homotopyHomologyEquiv A D x y (f + g) =
      homotopyHomologyEquiv A D x y f + homotopyHomologyEquiv A D x y g := by
  obtain ⟨f, rfl⟩ := (toHomotopy A D).map_surjective f
  obtain ⟨g, rfl⟩ := (toHomotopy A D).map_surjective g
  rw [← (toHomotopy A D).map_add, homotopyHomologyEquiv_map,
    homotopyHomologyEquiv_map, homotopyHomologyEquiv_map, closedHomEquiv_add,
    complexZeroHomologyClass_add]

lemma homotopyHomologyEquiv_smul (a : A)
    (f : (toHomotopy A D).obj x ⟶ (toHomotopy A D).obj y) :
    homotopyHomologyEquiv A D x y (a • f) = a • homotopyHomologyEquiv A D x y f := by
  obtain ⟨f, rfl⟩ := (toHomotopy A D).map_surjective f
  rw [← (toHomotopy A D).map_smul, homotopyHomologyEquiv_map,
    homotopyHomologyEquiv_map, closedHomEquiv_smul, complexZeroHomologyClass_smul]

def homotopyHomologyLinearEquiv :
    ((toHomotopy A D).obj x ⟶ (toHomotopy A D).obj y) ≃ₗ[A]
      (homObject A D x y).homology 0 where
  __ := homotopyHomologyEquiv A D x y
  map_add' := homotopyHomologyEquiv_add A D x y
  map_smul' := homotopyHomologyEquiv_smul A D x y

end SerrePositivity.DifferentialGraded
