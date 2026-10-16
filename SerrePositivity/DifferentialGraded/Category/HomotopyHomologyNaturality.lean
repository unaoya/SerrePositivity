module
public import SerrePositivity.DifferentialGraded.Category.HomotopyHomologyLinear
public import Mathlib.CategoryTheory.Enriched.Ordinary.Basic

/-! # cycleのホモロジー類の自然性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A]

def complexZeroCycle (K : Complex A) (c : zeroCycles K) : K.cycles 0 :=
  (K.cyclesIsoSc' (-1) 0 1 (by simp) (by simp)).inv
    ((K.sc' (-1) 0 1).moduleCatCyclesIso.inv c)

lemma complexZeroCycle_iCycles (K : Complex A) (c : zeroCycles K) :
    K.iCycles 0 (complexZeroCycle A K c) = c.val := by
  dsimp only [complexZeroCycle]
  rw [← ModuleCat.comp_apply, cyclesIsoSc'_inv_iCycles,
    ← ModuleCat.comp_apply, ShortComplex.moduleCatCyclesIso_inv_iCycles]
  rfl

lemma complexZeroHomologyClass_eq (K : Complex A) (c : zeroCycles K) :
    complexZeroHomologyClass A K c = K.homologyπ 0 (complexZeroCycle A K c) := by
  have h : (K.sc' (-1) 0 1).moduleCatLeftHomologyData.π ≫
      (complexZeroHomologyQuotientIso A K).hom =
      (K.sc' (-1) 0 1).moduleCatCyclesIso.inv ≫
        (K.cyclesIsoSc' (-1) 0 1 (by simp) (by simp)).inv ≫ K.homologyπ 0 := by
    dsimp only [complexZeroHomologyQuotientIso, Iso.trans_hom, Iso.symm_hom]
    rw [← ShortComplex.moduleCatCyclesIso_inv_π_assoc, π_homologyIsoSc'_inv]
  exact congrArg (fun f => f c) h

def complexMapZeroCycle {K L : Complex A} (f : K ⟶ L) (c : zeroCycles K) : zeroCycles L :=
  ⟨f.f 0 c.val, by
    have h := congrArg (fun g => g c.val) (f.comm 0 1)
    change L.d 0 1 (f.f 0 c.val) = 0
    change L.d 0 1 (f.f 0 c.val) = f.f 1 (K.d 0 1 c.val) at h
    have hc : K.d 0 1 c.val = 0 := c.property
    rw [hc, map_zero] at h
    exact h⟩

lemma complexZeroCycle_map {K L : Complex A} (f : K ⟶ L) (c : zeroCycles K) :
    cyclesMap f 0 (complexZeroCycle A K c) = complexZeroCycle A L (complexMapZeroCycle A f c) := by
  apply (ModuleCat.mono_iff_injective (L.iCycles 0)).1 inferInstance
  rw [← ModuleCat.comp_apply, cyclesMap_i, ModuleCat.comp_apply,
    complexZeroCycle_iCycles, complexZeroCycle_iCycles]
  rfl

lemma complexZeroHomologyClass_naturality {K L : Complex A} (f : K ⟶ L) (c : zeroCycles K) :
    homologyMap f 0 (complexZeroHomologyClass A K c) =
      complexZeroHomologyClass A L (complexMapZeroCycle A f c) := by
  rw [complexZeroHomologyClass_eq, ← ModuleCat.comp_apply, homologyπ_naturality,
    ModuleCat.comp_apply, complexZeroCycle_map, complexZeroHomologyClass_eq]

variable (D : Type v) [DGCategory A D] {x y z : ClosedCategory A D}
open MonoidalCategory

lemma closedHomEquiv_postcompose (f : x ⟶ y) (g : y ⟶ z) :
    complexMapZeroCycle A (eHomWhiskerLeft (Complex A) x g) (closedHomEquiv A D x y f) =
      closedHomEquiv A D x z (f ≫ g) := by
  have h : eHomEquiv (Complex A) f ≫ eHomWhiskerLeft (Complex A) x g =
      eHomEquiv (Complex A) (f ≫ g) := by
    rw [eHomEquiv_comp, eHomWhiskerLeft, ← Category.assoc, rightUnitor_inv_naturality]
    simp only [Category.assoc, tensorHom_def, unitors_inv_equal]
  apply Subtype.ext
  exact congrArg (fun k => (cycleFromUnit _ k).val) h

lemma homotopyHomologyEquiv_postcompose
    (f : (toHomotopy A D).obj x ⟶ (toHomotopy A D).obj y) (g : y ⟶ z) :
    homotopyHomologyEquiv A D x z (f ≫ (toHomotopy A D).map g) =
      homologyMap (eHomWhiskerLeft (Complex A) x g) 0 (homotopyHomologyEquiv A D x y f) := by
  obtain ⟨f, rfl⟩ := (toHomotopy A D).map_surjective f
  rw [← (toHomotopy A D).map_comp, homotopyHomologyEquiv_map, homotopyHomologyEquiv_map,
    complexZeroHomologyClass_naturality, closedHomEquiv_postcompose]

end SerrePositivity.DifferentialGraded
