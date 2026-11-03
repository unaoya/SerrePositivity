module
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison

/-! # U10b6c：全Hom endのcone比較の受入検査 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory HomologicalComplex CochainComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example (T : ModuleCategory A D) {M N : ModuleCategory A D} (f : M ⟶ N) :
    mappingCone (eHomWhiskerLeft (Complex A) T f) ≅
      moduleHom A D (ForgetEnrichment.to (Complex A) T)
        (ForgetEnrichment.to (Complex A) (moduleCone A D f)) := moduleHomConeIso A D T f

example (T : ModuleCategory A D) {M N : ModuleCategory A D} (f : M ⟶ N) (q : ℤ) :
    Function.LeftInverse (moduleHomConeInverseElement A D T f q)
      ((moduleHomConeComparison A D T f).f q) := moduleHomConeComparison_leftInverse A D T f q

example (T : ModuleCategory A D) {M N : ModuleCategory A D} (f : M ⟶ N) (q : ℤ) :
    Function.RightInverse (moduleHomConeInverseElement A D T f q)
      ((moduleHomConeComparison A D T f).f q) := moduleHomConeComparison_rightInverse A D T f q

example (T : ModuleCategory A D) {M N : ModuleCategory A D} (f : M ⟶ N) :
    mappingCone.inr (eHomWhiskerLeft (Complex A) T f) ≫ moduleHomConeComparison A D T f =
      eHomWhiskerLeft (Complex A) T (moduleConeInr A D f) := moduleHomConeComparison_inr A D T f

end SerrePositivity.DifferentialGraded.Checks

open SerrePositivity.DifferentialGraded
#print axioms complexConeElementMk
#print axioms complexConeElementMk_fst
#print axioms complexConeElementMk_snd
#print axioms complexConeElement_ext
#print axioms complexConeElementMk_eta
#print axioms moduleHomConeLeftCochain
#print axioms moduleHomConeLeftCochain_d
#print axioms moduleHomConeLeftCochain_π
#print axioms moduleHomConeComparison
#print axioms moduleHomConeComparison_inr
#print axioms moduleHomConeComparison_apply_π
#print axioms moduleHomConeInverseElement
#print axioms moduleHomConeInverseElement_fst_π
#print axioms moduleHomConeInverseElement_snd_π
#print axioms moduleHomConeComparison_rightInverse
#print axioms moduleHomConeComparison_leftInverse
#print axioms moduleHomConeComparison_bijective
#print axioms moduleHomConeComparison_isIso
#print axioms moduleHomConeIso
