module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ModuleDerivedClosedFamilies
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseSimplexConstantFamilies
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseModuleDerivedFamilies
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseDerivedCompatibility

/-! 共通宇宙での閉 augmentation の定値族は、元の実導来辺の同じ区間図式。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]

lemma dgGluingUniverseModuleDerivedFamilyInterval_closed (A : Complex R)
    {P Q : RightModule R C}
    (s : ForgetEnrichment.of (Complex R) P ⟶ ForgetEnrichment.of (Complex R) Q) :
    intervalMappingUncurry (dgGluingUniverseModuleDerivedFamilyInterval.{u, v, w} R C
      (SSet.const (X := complexPinchedSpace.{u, max (u + 1) v} A)
        (pinchedClosedVertex R (RightModule R C) s))) =
    fst (Δ[1] : SSet.{max (u + 1) v w})
        ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
          (complexPinchedSpace.{u, max u v w} A)) ≫
      SSet.yonedaEquiv.symm ((dgGluingUniverseModuleDerivedComparison.{u, v, w} R C).app
        (Opposite.op ⦋1⦌) (ULift.up (dgClosedEdge R (RightModule R C) s).edge)) := by
  rw [← dgGluingUniverseModuleDerivedFamilyInterval_evaluate.{u, v, w} R C,
    dgGluingModuleDerivedFamilyInterval_closed R C,
    dgGluingUliftSimplexFamily_constant, whiskerLeft_fst_assoc]
  rfl

end SerrePositivity.InfinityCategories
