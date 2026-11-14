module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.IntervalEndpointTransport
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalMappingPostIso
/-!
概要：区間後合成と両端点の同じ厳密輸送を照合する。
方針：端点等式を消去し、元の全区間族の後合成へ帰着する。
規約：元の全パラメーターと端点輸送を保持する。
使われ方：正本の底座標を元の導来二作用へ厳密に正規化する。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory SSet
open scoped _root_.Simplicial
lemma dgGluingIntervalPostOfEq_endpoint {X Y : SSet.{u}} (p : X ⟶ Y)
    (x y : X _⦋0⦌) {a b : Y _⦋0⦌} (ha : p.app _ x = a) (hb : p.app _ y = b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPost p x y ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.intervalEndpointIso ha hb).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPostOfEq p x y ha hb := by
  subst a
  subst b
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.intervalEndpointIso, Iso.refl_hom, Category.comp_id]
  rfl

lemma dgGluingIntervalPostOfEq_endpoint_naturality {X Y : SSet.{u}} (p : X ⟶ Y)
    {x y x' y' : X _⦋0⦌} (hx : x = x') (hy : y = y')
    {a b : Y _⦋0⦌} (ha : p.app _ x' = a) (hb : p.app _ y' = b) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.intervalEndpointIso hx hy).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPostOfEq p x y rfl rfl ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.intervalEndpointIso ((congrArg (p.app _) hx).trans ha)
        ((congrArg (p.app _) hy).trans hb)).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPostOfEq p x' y' ha hb := by
  subst x'
  subst y'
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.intervalEndpointIso, Iso.refl_inv, Category.id_comp]
  exact dgGluingIntervalPostOfEq_endpoint p x y ha hb
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
