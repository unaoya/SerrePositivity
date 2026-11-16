module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedHomPinchedComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalFamilyInvariance
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanHomotopyEquivalence

/-! 既存の同じcoslice・pinched・edgewiseの三角形を全interval族の等式へ移す。 -/

@[expose] public section
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- 同じ指定三角形の、任意パラメータの全族での式。 -/
lemma cosliceFiberRightMappingEquivalence_interval_family {K C : SSet.{u}} [Quasicategory C]
    {x y : C _⦋0⦌} (f : K ⟶ vertexFiber (sliceUnderProjection (yonedaEquiv.symm x)) y) :
    intervalFamilyHom (f ≫ (cosliceFiberRightMappingEquivalence x y).hom ≫
      pinchedHomToIntervalMappingSpace x y) =
      intervalFamilyHom (f ≫ cosliceFiberToIntervalMappingSpace x y) := by
  have e := ((pinchedHomToIntervalMappingSpace_isQCatEquivalence x y).choose.invHomIso).precomp
    (f ≫ cosliceFiberToIntervalMappingSpace x y)
  apply intervalFamilyHom_eq_of_homotopy
  simpa only [cosliceFiberRightMappingEquivalence, QCatEquivalence.trans,
    QCatEquivalence.symm, IsQCatEquivalence.choose, Category.assoc, Category.comp_id] using
    e.simplicialHomotopy
/-- 同じ指定三角形の、任意パラメータの全族での式。 -/
lemma twistedArrowHomPinchedEquivalence_coslice_interval_family {K C : SSet.{u}} [Quasicategory C]
    {x y : C _⦋0⦌} (f : K ⟶ vertexFiber (sliceUnderProjection (yonedaEquiv.symm x)) y) :
    intervalFamilyHom (f ≫ cosliceTwistedHomMap x y ≫
      (twistedArrowHomPinchedEquivalence x y).hom ≫ pinchedHomToIntervalMappingSpace x y) =
      intervalFamilyHom (f ≫ cosliceFiberToIntervalMappingSpace x y) := by
  have e := ((twistedArrowHomPinchedEquivalence_coslice x y).precomp f).postcomp
    (pinchedHomToIntervalMappingSpace x y)
  have h := intervalFamilyHom_eq_of_homotopy e.simplicialHomotopy
  exact h.trans (cosliceFiberRightMappingEquivalence_interval_family f)
/-- 同じ指定三角形の、任意パラメータの全族での式。 -/
lemma twistedArrowHomPinchedEquivalence_interval_family {K C : SSet.{u}} [Quasicategory C]
    {x y : C _⦋0⦌} (g : K ⟶ twistedArrowHomSpace x y) :
    intervalFamilyHom (g ≫ (twistedArrowHomPinchedEquivalence x y).hom ≫
      pinchedHomToIntervalMappingSpace x y) =
      intervalFamilyHom (g ≫ (cosliceTwistedHomMap_isQCatEquivalence x y).choose.inv ≫
        cosliceFiberToIntervalMappingSpace x y) := by
  simpa only [twistedArrowHomPinchedEquivalence, QCatEquivalence.trans,
    QCatEquivalence.symm, Category.assoc] using
      (cosliceFiberRightMappingEquivalence_interval_family (g ≫ (cosliceTwistedHomMap_isQCatEquivalence x y).choose.inv))
/-- 同じ指定三角形の、任意パラメータの全族での式。 -/
lemma twistedArrowHomOppositePinchedEquivalence_edgewise_interval_family {K C : SSet.{u}} [Quasicategory C]
    {x y : C _⦋0⦌} (g : K ⟶ edgewiseSubdivision (twistedArrowHomSpace x y)) :
    intervalFamilyHom (g ≫ edgewiseLeft (twistedArrowHomSpace x y) ≫
      (twistedArrowHomOppositePinchedEquivalence x y).hom ≫ pinchedHomToIntervalMappingSpace x y) =
      intervalFamilyHom (g ≫ edgewiseRight (twistedArrowHomSpace x y) ≫
        (twistedArrowHomPinchedEquivalence x y).hom ≫ pinchedHomToIntervalMappingSpace x y) := by
  have e := ((twistedArrowHomOppositePinchedEquivalence_edgewise x y).precomp g).postcomp
    (pinchedHomToIntervalMappingSpace x y)
  exact intervalFamilyHom_eq_of_homotopy e.simplicialHomotopy

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

end
