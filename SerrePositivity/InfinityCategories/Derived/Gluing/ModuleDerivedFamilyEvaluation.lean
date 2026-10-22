module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeDerivedCoefficientTriangles

/-! 同じ導来 Hom 族と、そのホモトピーの全区間での評価。 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]

def dgGluingModuleDerivedFamilyInterval {K : SSet.{max (u + 1) v}} {P Q : RightModule R C}
    (f : K ⟶ DGNerve.pinchedHom R (RightModule R C) P Q) :=
  (f ≫ pinchedHomMap
    (dgModuleResolvedInfinity R (RightModule R C) C (DGFunctor.id (RightModule R C)))
    (DGNerve.Simplex.vertex P) (DGNerve.Simplex.vertex Q)) ≫
      pinchedHomToIntervalMappingSpace _ _

lemma dgGluingModuleDerivedFamilyHomotopy_evaluate
    {K : SSet.{max (u + 1) v}} {P Q : RightModule R C}
    (f : K ⟶ DGNerve.pinchedHom R (RightModule R C) P Q) :
    (β_ (Δ[1] : SSet.{max (u + 1) v}) K).hom ≫
        (dgGluingModuleDerivedFamilyHomotopy R C f).h =
      intervalMappingUncurry (dgGluingModuleDerivedFamilyInterval R C f) := by
  simp only [dgGluingModuleDerivedFamilyHomotopy, intervalFamilyHomotopy,
    ← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]
  rfl

end SerrePositivity.InfinityCategories
