module
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseModuleDerivedFamilies

/-! 複体パラメーターの元の鎖写像による制限は、同じ導来全区間族の構成と可換。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]

lemma dgGluingUniverseModuleDerivedFamilyInterval_precomp {A B : Complex R}
    {P Q : RightModule R C} (φ : A ⟶ B)
    (f : complexPinchedSpace.{u, max (u + 1) v} B ⟶
      DGNerve.pinchedHom R (RightModule R C) P Q) :
    (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
        (complexPinchedMap.{u, max u v w} φ) ≫
      dgGluingUniverseModuleDerivedFamilyInterval.{u, v, w} R C f =
    dgGluingUniverseModuleDerivedFamilyInterval.{u, v, w} R C
      (complexPinchedMap.{u, max (u + 1) v} φ ≫ f) := by
  rw [dgGluingUniverseModuleDerivedFamilyInterval, ← Category.assoc,
    dgGluingComplexPinchedUniverseIso_naturality, Category.assoc]
  simp only [dgGluingUniverseModuleDerivedFamilyInterval, Functor.map_comp, Category.assoc]

end SerrePositivity.InfinityCategories
