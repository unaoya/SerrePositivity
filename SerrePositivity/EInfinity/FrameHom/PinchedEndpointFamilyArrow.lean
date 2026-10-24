module
public import SerrePositivity.InfinityCategories.Derived.PinchedEndpointTransport
public import SerrePositivity.InfinityCategories.F1B.MappingSpaces.MappingParameterNaturality
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.RightIntervalEquivalence
/-!
概要：pinched 全族の端点等式輸送は、元の全関手射の Arrow を保つ。
方針：端点の等式を消去し、同じ全族の恒等作用に帰着する。
規約：全パラメータと元の全単体を保持する。
使われ方：複体の元の導来源と ambient 表示の全族比較。
-/
@[expose] public section
universe u
namespace SerrePositivity.EInfinity.FrameHom
open CategoryTheory SSet SerrePositivity.InfinityCategories
open scoped Simplicial
/-- 概要：元の全 pinched 族の端点等式輸送は同じ全 Arrow を表す。
方針：端点等式を消去する。
規約：同じパラメータを保持。使われ方：実複体屋根の定値端点への回収。 -/
lemma pinchedEndpointFamily_arrow {K X : SSet.{u}}
    {x y x' y' : X.obj (Opposite.op ⦋0⦌)} (hx : x = x') (hy : y = y')
    (f : K ⟶ pinchedHom x y) :
    Arrow.mk (intervalFamilyHom (f ≫ (pinchedEndpointIso hx hy).hom ≫
      pinchedHomToIntervalMappingSpace x' y')) =
    Arrow.mk (intervalFamilyHom (f ≫ pinchedHomToIntervalMappingSpace x y)) := by
  cases hx
  cases hy
  simp only [pinchedEndpointIso, Iso.refl_hom, Category.id_comp]
end SerrePositivity.EInfinity.FrameHom
