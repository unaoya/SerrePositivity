module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Roof.PinchedEndpointTransport
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.MappingParameterNaturality
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.RightIntervalEquivalence
/-!
概要：pinched 全族の端点等式輸送は、元の全関手射の Arrow を保つ。
方針：端点の等式を消去し、同じ全族の恒等作用に帰着する。
規約：全パラメータと元の全単体を保持する。
使われ方：複体の元の導来源と ambient 表示の全族比較。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open CategoryTheory SSet _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
/-- 概要：元の全 pinched 族の端点等式輸送は同じ全 Arrow を表す。
方針：端点等式を消去する。
規約：同じパラメータを保持。使われ方：実複体屋根の定値端点への回収。 -/
lemma pinchedEndpointFamily_arrow {K X : SSet.{u}}
    {x y x' y' : X.obj (Opposite.op ⦋0⦌)} (hx : x = x') (hy : y = y')
    (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y) :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (f ≫ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Roof.pinchedEndpointIso hx hy).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace x' y')) =
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace x y)) := by
  cases hx
  cases hy
  simp only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Roof.pinchedEndpointIso, Iso.refl_hom, Category.id_comp]
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
