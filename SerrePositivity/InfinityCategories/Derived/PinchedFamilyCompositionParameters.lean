module
public import SerrePositivity.InfinityCategories.Derived.PinchedFamilyComposition
public import SerrePositivity.InfinityCategories.F1B.MappingParameterNaturality
/-!
概要：任意パラメータ族の合成方程式を、任意のパラメータ制限に沿って保つ。
方針：関手圏の前合成の合成保存と実区間族の自然性を使う。
規約：全パラメータと元の合成方程式を保持する。使われ方：全降下選択空間との積での合成則。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
/-- 三実 pinched Hom 族の合成方程式は、任意のパラメータ制限に自然。 -/
lemma pinchedFamilyHom_comp_precomp {L K X : SSet.{u}} {x y z : X _⦋0⦌}
    (p : L ⟶ K) (f : K ⟶ pinchedHom x y) (g : K ⟶ pinchedHom y z)
    (c : K ⟶ pinchedHom x z)
    (hc : intervalFamilyHom (f ≫ pinchedHomToIntervalMappingSpace x y) ≫
      intervalFamilyHom (g ≫ pinchedHomToIntervalMappingSpace y z) =
        intervalFamilyHom (c ≫ pinchedHomToIntervalMappingSpace x z)) :
    intervalFamilyHom ((p ≫ f) ≫ pinchedHomToIntervalMappingSpace x y) ≫
      intervalFamilyHom ((p ≫ g) ≫ pinchedHomToIntervalMappingSpace y z) =
        intervalFamilyHom ((p ≫ c) ≫ pinchedHomToIntervalMappingSpace x z) := by
  have h := congrArg (hoFunctor.map ((pre p).app X)).toFunctor.map hc
  simpa only [Functor.map_comp, Category.assoc, intervalFamilyHom_precomp,
    intervalFamilyHomPrecomp] using h
end SerrePositivity.InfinityCategories
