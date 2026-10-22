module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ModuleDerivedFamilyEvaluation
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniversePinchedIntervalFamilies
public import SerrePositivity.InfinityCategories.Derived.Gluing.ComplexPinchedUniverseNaturality

/-! 元の複体パラメーターと実導来 Hom 作用を、共通宇宙の同じ区間族へ移す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]

def dgGluingUniverseModuleDerivedFamilyInterval {A : Complex R} {P Q : RightModule R C}
    (f : complexPinchedSpace.{u, max (u + 1) v} A ⟶
      DGNerve.pinchedHom R (RightModule R C) P Q) :=
  (dgGluingComplexPinchedUniverseIso.{u, max u v w, max (u + 1) v} A).hom ≫
    (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).map
      (f ≫ pinchedHomMap
        (dgModuleResolvedInfinity R (RightModule R C) C (DGFunctor.id (RightModule R C)))
        (DGNerve.Simplex.vertex P) (DGNerve.Simplex.vertex Q)) ≫
      (uliftPinchedHomIso
        ((dgModuleResolvedInfinity R (RightModule R C) C (DGFunctor.id (RightModule R C))).app
          (Opposite.op ⦋0⦌) (DGNerve.Simplex.vertex P))
        ((dgModuleResolvedInfinity R (RightModule R C) C (DGFunctor.id (RightModule R C))).app
          (Opposite.op ⦋0⦌) (DGNerve.Simplex.vertex Q))).hom ≫
        pinchedHomToIntervalMappingSpace _ _

lemma dgGluingUniverseModuleDerivedFamilyInterval_evaluate {A : Complex R}
    {P Q : RightModule R C}
    (f : complexPinchedSpace.{u, max (u + 1) v} A ⟶
      DGNerve.pinchedHom R (RightModule R C) P Q) :
    ((Δ[1] : SSet.{max (u + 1) v w}) ◁
        (dgGluingComplexPinchedUniverseIso.{u, max u v w, max (u + 1) v} A).hom) ≫
      dgGluingUliftSimplexFamily.{max (u + 1) v, max (u + 1) v w} 1
        (intervalMappingUncurry (dgGluingModuleDerivedFamilyInterval R C f)) =
    intervalMappingUncurry (dgGluingUniverseModuleDerivedFamilyInterval.{u, v, w} R C f) := by
  rw [dgGluingModuleDerivedFamilyInterval, dgGluingUliftPinchedIntervalFamily,
    ← intervalMappingUncurry_precomp]
  rfl

end SerrePositivity.InfinityCategories
