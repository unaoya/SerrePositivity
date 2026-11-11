module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.IntervalEndpointTransport
/-!
概要：区間写像空間の端点等式による輸送は元の全区間族を変えない。
方針：端点等式を消去し、同じ恒等射の後合成へ帰着する。
規約：全パラメーターを保持する。
使われ方：正本の底座標の端点輸送を二作用の厳密照合から除く。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory SSet
open scoped _root_.Simplicial
lemma dgGluingIntervalEndpointIso_hom_uncurry {T X : SSet.{u}}
    {x y x' y' : X _⦋0⦌} (hx : x = x') (hy : y = y')
    (h : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (h ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.intervalEndpointIso hx hy).hom) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry h := by
  subst x'
  subst y'
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.intervalEndpointIso, Iso.refl_hom, Category.comp_id]
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
