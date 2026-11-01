module
public import SerrePositivity.InfinityCategories.F1B.PinchedFamilyHomotopy
public import SerrePositivity.InfinityCategories.Core.Roof.PinchedEndpointTransport
/-!
概要：実 pinched Hom 三族の合成方程式を、三つの端点の等式輸送に沿って保つ。
方針：端点の三等式に帰納法を使い、元の同じ合成方程式へ戻す。
規約：標的の充填性・パラメータの有限性を仮定しない。使われ方：商の標準頂点での三評価族。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open scoped Simplicial
/-- 三端点の等式輸送は、同じパラメータ関手圏の実三族の合成方程式を保つ。 -/
lemma pinchedFamilyHom_comp_endpointTransport {K X : SSet.{u}} {x y z x' y' z' : X _⦋0⦌}
    (hx : x = x') (hy : y = y') (hz : z = z')
    (f : K ⟶ pinchedHom x y) (g : K ⟶ pinchedHom y z) (c : K ⟶ pinchedHom x z)
    (hc : intervalFamilyHom (f ≫ pinchedHomToIntervalMappingSpace x y) ≫
      intervalFamilyHom (g ≫ pinchedHomToIntervalMappingSpace y z) =
        intervalFamilyHom (c ≫ pinchedHomToIntervalMappingSpace x z)) :
    intervalFamilyHom ((f ≫ (pinchedEndpointIso hx hy).hom) ≫
      pinchedHomToIntervalMappingSpace x' y') ≫
    intervalFamilyHom ((g ≫ (pinchedEndpointIso hy hz).hom) ≫
      pinchedHomToIntervalMappingSpace y' z') =
    intervalFamilyHom ((c ≫ (pinchedEndpointIso hx hz).hom) ≫
      pinchedHomToIntervalMappingSpace x' z') := by
  subst x'
  subst y'
  subst z'
  simpa only [pinchedEndpointIso, Iso.refl_hom, Category.comp_id] using hc
end SerrePositivity.InfinityCategories
