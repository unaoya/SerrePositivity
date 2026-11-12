module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.PointCoslicePostIso
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PointedFiberTransportCoordinates

/-!
概要：coslice の底の変更と端点表示の変更を、元の錐の射で計算する。
方針：等号による移送は消去し、後合成の実際の単体作用を読む。
規約：任意の底・次数で成り立ち、充填性は要求しない。
使われ方：反転した合成輸送と左 Hom 比較の全次数の照合。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 固定図式の等号による coslice の移送は元の錐の射を変えない。 -/
lemma sliceUnder_eqToHom_app_val {K X : SSet.{u}} {p q : K ⟶ X} (h : p = q)
    (n : ℕ) (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) _⦋n⦌) :
    ((eqToHom (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder h)).app (Opposite.op ⦋n⦌) s).val = s.val := by
  subst q
  rfl

/-- fiber の両端点の表示変更は元の錐の射を変えない。 -/
lemma cosliceFiberVerticesIso_app_val {X : SSet.{u}} {x y x' y' : X _⦋0⦌}
    (hx : x = x') (hy : y = y') (n : ℕ)
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) y) _⦋n⦌) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cosliceFiberVerticesIso hx hy).hom.app (Opposite.op ⦋n⦌) s).val.val = s.val.val := by
  subst x'
  subst y'
  rfl

/-- 底の同型で移した頂点 coslice の射は元の錐への後合成そのもの。 -/
lemma pointCoslicePostIso_app_val {B D : SSet.{u}} (d : B ≅ D) (z : B _⦋0⦌)
    (n : ℕ) (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm z)) _⦋n⦌) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointCoslicePostIso d z).hom.app (Opposite.op ⦋n⦌) s).val = s.val ≫ d.hom := by
  change ((eqToHom (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv_symm_comp z d.hom))).app
    (Opposite.op ⦋n⦌) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp _ d.hom).app _ s)).val = _
  rw [sliceUnder_eqToHom_app_val (SSet.yonedaEquiv_symm_comp z d.hom)]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
