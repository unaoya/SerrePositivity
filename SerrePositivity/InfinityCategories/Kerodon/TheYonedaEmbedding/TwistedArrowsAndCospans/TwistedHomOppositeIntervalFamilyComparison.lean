module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedHomIntervalFamilyComparison

/-! 同じ反対twisted Homの指定比較を、合成を含む全interval族へ移す。 -/

@[expose] public section
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
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

/-- 同じ指定逆と三角形の、全パラメータでの合成・移送の法則。 -/
lemma twistedArrowHomOppositePinchedEquivalence_interval_family {K C : SSet.{u}} [Quasicategory C]
    {x y : C _⦋0⦌} (g : K ⟶ (twistedArrowHomSpace x y).op) :
    intervalFamilyHom (g ≫ (twistedArrowHomOppositePinchedEquivalence x y).hom ≫
      pinchedHomToIntervalMappingSpace x y) =
      intervalFamilyHom (g ≫ (isQCatEquivalence_of_trivialKanFibration
        (edgewiseLeft (twistedArrowHomSpace x y))).choose.inv ≫
        edgewiseRight (twistedArrowHomSpace x y) ≫
        (cosliceTwistedHomMap_isQCatEquivalence x y).choose.inv ≫
        cosliceFiberToIntervalMappingSpace x y) := by
  simpa only [twistedArrowHomOppositePinchedEquivalence, QCatEquivalence.trans,
    QCatEquivalence.symm, IsQCatEquivalence.choose, Category.assoc] using
      (twistedArrowHomPinchedEquivalence_interval_family
        (g ≫ (isQCatEquivalence_of_trivialKanFibration
          (edgewiseLeft (twistedArrowHomSpace x y))).choose.inv ≫
          edgewiseRight (twistedArrowHomSpace x y)))
/-- 同じ指定逆と三角形の、全パラメータでの合成・移送の法則。 -/
lemma twistedArrowHomOppositePinchedEquivalence_interval_family_comp {K T C : SSet.{u}} [Quasicategory C]
    {x y : C _⦋0⦌} (f : K ⟶ T) (e : T ⟶ (twistedArrowHomSpace x y).op)
    (h : T ⟶ Basic.pinchedHom x y)
    (hh : h = e ≫ (twistedArrowHomOppositePinchedEquivalence x y).hom) :
    intervalFamilyHom ((f ≫ h) ≫ pinchedHomToIntervalMappingSpace x y) =
      intervalFamilyHom (f ≫ e ≫ (isQCatEquivalence_of_trivialKanFibration
        (edgewiseLeft (twistedArrowHomSpace x y))).choose.inv ≫
        edgewiseRight (twistedArrowHomSpace x y) ≫
        (cosliceTwistedHomMap_isQCatEquivalence x y).choose.inv ≫
        cosliceFiberToIntervalMappingSpace x y) := by
  subst h
  simpa only [Category.assoc] using twistedArrowHomOppositePinchedEquivalence_interval_family (f ≫ e)


end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

end
