module
public import SerrePositivity.DifferentialGraded.Derived.HomOutPrecomposition

/-! # U10b7c：導来Homの前合成・自然同型・ホモトピー独立性 -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

example {M N : ModuleCategory A D} (hM : moduleHomotopicallyProjective A D M)
    (hN : moduleHomotopicallyProjective A D N) (f : M ⟶ N) (hf : moduleQuasiIso A D f) :
    moduleDerivedHomOut A D N hN ≅ moduleDerivedHomOut A D M hM :=
  moduleDerivedHomOutPrecompIso A D hM hN f hf

example {M N : ModuleCategory A D} (hM : moduleHomotopicallyProjective A D M)
    (hN : moduleHomotopicallyProjective A D N) {f g : M ⟶ N}
    (h : (moduleToHomotopy A D).map f = (moduleToHomotopy A D).map g) :
    moduleDerivedHomOutPrecomp A D hM hN f = moduleDerivedHomOutPrecomp A D hM hN g :=
  moduleDerivedHomOutPrecomp_eq_of_homotopy_map_eq A D hM hN h

example {M N P : ModuleCategory A D} (hM : moduleHomotopicallyProjective A D M)
    (hN : moduleHomotopicallyProjective A D N) (hP : moduleHomotopicallyProjective A D P)
    (f : M ⟶ N) (g : N ⟶ P) :
    moduleDerivedHomOutPrecomp A D hM hP (f ≫ g) =
      moduleDerivedHomOutPrecomp A D hN hP g ≫ moduleDerivedHomOutPrecomp A D hM hN f :=
  moduleDerivedHomOutPrecomp_comp A D hM hN hP f g

end SerrePositivity.DifferentialGraded.Checks

open SerrePositivity.DifferentialGraded
#print axioms moduleDerivedHomOutEnrichedComputation
#print axioms moduleHomOutToDerivedPrecomp
#print axioms moduleHomOutToDerivedPrecomp_app
#print axioms moduleDerivedHomOutPrecomp
#print axioms moduleDerivedHomOutPrecomp_app
#print axioms moduleDerivedHomOutPrecomp_id
#print axioms moduleDerivedHomOutPrecomp_comp
#print axioms moduleDerivedHomOutPrecomp_eq_of_homotopy
#print axioms moduleDerivedHomOutPrecomp_eq_of_homotopy_map_eq
#print axioms moduleDerivedHomOutPrecomp_isIso
#print axioms moduleDerivedHomOutPrecompIso
