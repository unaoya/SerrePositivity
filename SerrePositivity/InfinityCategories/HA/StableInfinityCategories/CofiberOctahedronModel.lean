module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberOctahedronTriangleComparisons
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.OctahedronFromComparisons
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PretriangulatedInstance

/-! # 二長方形からの八面体模型

概要：安定 ∞ 圏の二長方形の図式から Mathlib の八面体を持つ模型を得る。
方針：構成済みの二つの三角形比較と最後の列を、一般の前三角圏の組み立て補題へ渡す。
規約：最初の二射は元の列・次の列の第一射と Arrow として等しい。
使われ方：任意の二射に対する八面体公理の模型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Pretriangulated Triangulated MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：指定 cofiber 列の二長方形の図式は八面体の模型を与える。
方針：四つの三角形の所属と二比較の七つの Arrow の照合、第三射の合成式を合わせる。
規約：表示の違いを模型の存在定理で吸収する。使われ方：TR4 の代表上での完成。 -/
lemma CofiberOctahedronDiagram.octahedronModel {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    {t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X} (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t) {τ : (Δ[2] : SSet.{u}) ⟶ X}
    (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberOctahedronDiagram t τ) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.OctahedronModel (Arrow.mk t.hoShortComplex.f)
      (Arrow.mk d.second.outerZeroTriangle.hoShortComplex.f) := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_octahedron_of_triangle_comparisons
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle t ht)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle d.first.outerZeroTriangle d.first.outer_isCofiber)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle d.second.outerZeroTriangle d.second.outer_isCofiber)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle d.second.rightZeroTriangle d.second.right_isCofiber)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle_mem_cofiberDistinguishedTriangles t ht)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle_mem_cofiberDistinguishedTriangles _ d.first.outer_isCofiber)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle_mem_cofiberDistinguishedTriangles _ d.second.outer_isCofiber)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle_mem_cofiberDistinguishedTriangles _ d.second.right_isCofiber)
    (d.first.triangleMorphism ht) d.nextTriangleMorphism d.second.sourceHom
    (d.first.triangleMorphism_source_arrow ht) (d.firstTriangle_middle_arrow ht)
    d.nextTriangle_source_arrow d.nextTriangle_middle_arrow (d.last_first_arrow ht)
    d.last_second_arrow d.last_source_arrow
  exact congrArg Arrow.mk d.second.triangle_connecting_comp

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
