module
public import SerrePositivity.InfinityCategories.Derived.PinchedFamilyPostcomposition

/-! 同じ全パラメーターの合成方程式を、指定された ∞ 関手の実 Hom 作用で移す。 -/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial

lemma dgGluingPinchedFamilyComposition_postcomp {K X Y : SSet.{u}} (F : X ⟶ Y)
    {x y z : X _⦋0⦌} (f : K ⟶ pinchedHom x y) (g : K ⟶ pinchedHom y z)
    (c : K ⟶ pinchedHom x z)
    (hc : intervalFamilyHom (f ≫ pinchedHomToIntervalMappingSpace x y) ≫
      intervalFamilyHom (g ≫ pinchedHomToIntervalMappingSpace y z) =
        intervalFamilyHom (c ≫ pinchedHomToIntervalMappingSpace x z)) :
    intervalFamilyHom ((f ≫ pinchedHomMap F x y) ≫ pinchedHomToIntervalMappingSpace _ _) ≫
      intervalFamilyHom ((g ≫ pinchedHomMap F y z) ≫ pinchedHomToIntervalMappingSpace _ _) =
        intervalFamilyHom ((c ≫ pinchedHomMap F x z) ≫ pinchedHomToIntervalMappingSpace _ _) := by
  rw [pinchedFamilyHom_postcomp, pinchedFamilyHom_postcomp, pinchedFamilyHom_postcomp]
  have h := congrArg ((hoFunctor.map ((ihom K).map F)).toFunctor.map) hc
  rw [Functor.map_comp] at h
  exact roofConjugatedEvaluation_fac (constantFunctorCompIso K x F)
    (constantFunctorCompIso K y F) (constantFunctorCompIso K z F) _ _ _ h

end SerrePositivity.InfinityCategories
