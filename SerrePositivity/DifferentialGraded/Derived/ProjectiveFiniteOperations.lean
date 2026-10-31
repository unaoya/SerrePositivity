module
public import SerrePositivity.DifferentialGraded.Functor.ModuleShiftOpposite
public import SerrePositivity.DifferentialGraded.Derived.GradedExtensionProjective
public import SerrePositivity.DifferentialGraded.Module.ConeGradedSplit
public import SerrePositivity.DifferentialGraded.Module.Biproduct
public import SerrePositivity.DifferentialGraded.Module.ShiftCoherence
public import SerrePositivity.HomologicalAlgebra.Complex.ConeLES

/-! # 主Homによる射影性の有限操作に対する閉性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 主Hom endの始域shiftは、通常の複体の逆shiftに対応する。 -/
def moduleHomSourceShiftIso (M N : RightModule A D) (s : ℤ) :
    moduleHom A D (shiftModule s M) N ≅ (moduleHom A D M N)⟦-s⟧ :=
  DGFunctor.moduleShiftOppImageIso A D
    ((representable A (D := RightModule A D) N).toFunctor) s M

lemma moduleHomotopicallyProjective_shift {M : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M) (s : ℤ) :
    moduleHomotopicallyProjective A D (M⟦s⟧) := by
  intro N hN
  exact cochainAcyclic_of_iso (cochainAcyclic_shift (hM N hN) (-s))
    (moduleHomSourceShiftIso A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) N) s).symm

lemma moduleHomotopicallyProjective_cone {M N : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M) (hN : moduleHomotopicallyProjective A D N)
    (f : M ⟶ N) : moduleHomotopicallyProjective A D (moduleCone A D f) :=
  (moduleConeGradedSplit A D f).homotopicallyProjective A D hN
    (moduleHomotopicallyProjective_shift A D hM 1)

lemma moduleHomotopicallyProjective_biprod {M N : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M) (hN : moduleHomotopicallyProjective A D N) :
    moduleHomotopicallyProjective A D (moduleBiprod A D M N) := by
  have hσ := moduleCoproduct_homotopicallyProjective A D
    (fun j : WalkingPair => WalkingPair.casesOn j M N) (by
      intro j
      cases j
      · exact hM
      · exact hN)
  change moduleHomotopicallyProjective A D (M ⨿ N) at hσ
  exact moduleHomotopicallyProjective_of_iso A D
    ((biprod.isoCoprod M N).symm ≪≫ (moduleBiprodIso A D M N).symm) hσ

end SerrePositivity.DifferentialGraded
