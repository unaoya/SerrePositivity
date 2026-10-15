module
public import SerrePositivity.DifferentialGraded.Module.ConeElements
public import SerrePositivity.DifferentialGraded.Module.Postcomposition

/-! # U10b6b：coneの斉次包含・射影と全次数後合成 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) (moduleCone A D f))).d (-1) 0
        (moduleConeInlElement A D f) =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A)
        (f ≫ moduleConeInr A D f))).val := moduleConeInlElement_d A D f

example (T M N : RightModule A D) {p q n : ℤ}
    (g : (moduleHom A D M N).X p) (z : (moduleHom A D T M).X q) (hn : q + p = n) :
    (((modulePostcompositionMap A D T M N).f p g).v q n hn) z =
      compose A (x := T) (y := M) (z := N) g z hn :=
  modulePostcompositionMap_apply A D T M N g z hn

example (T : ModuleCategory A D) {M N : ModuleCategory A D} (f : M ⟶ N) :
    (modulePostcompositionMap A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) N)).f 0
        (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val =
      Cochain.ofHom (eHomWhiskerLeft (Complex A) T f) := modulePostcompositionMap_closed A D T f

end SerrePositivity.DifferentialGraded.Checks

open SerrePositivity.DifferentialGraded
#print axioms moduleConeInlElement
#print axioms moduleConeInlElement_π
#print axioms moduleConeFstElement
#print axioms moduleConeFstElement_π
#print axioms moduleConeSndElement
#print axioms moduleConeSndElement_π
#print axioms moduleConeInlElement_d
#print axioms moduleConeFstElement_d
#print axioms moduleHomCompose_π
#print axioms moduleHomWhiskerLeft_apply_π
#print axioms modulePostcompositionMap
#print axioms modulePostcompositionMap_apply
#print axioms modulePostcompositionMap_d
#print axioms modulePostcompositionMap_closed
