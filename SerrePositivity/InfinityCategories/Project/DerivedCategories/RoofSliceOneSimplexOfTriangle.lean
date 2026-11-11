module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofSliceTetrahedronInverse

/-! # 終頂点を固定した三角形から実 over 辺を回収する

概要：指定 over 頂点の分母辺を零面に持つ三角形を実 over の一単体へ戻す。
方針：点との join の標準単体同型を使い、回収三角形を厳密に保存する。
規約：三角形の存在は入力。使われ方：頂点ごとの固定脚の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
open scoped _root_.Simplicial
variable {X : SSet.{u}} (a : Δ[0] ⟶ X)

/-- over 頂点の分母辺は、その終点で指定点へ制限される。 -/
lemma roofPointSliceVertexEdge_fixed (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a) _⦋0⦌) :
    stdSimplex.δ (0 : Fin 2) ≫
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge a v).edge = a := by
  apply SSet.yonedaEquiv.injective
  rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge a v).tgt_eq

/-- 指定零面を持つ三角形を、終頂点を固定した実 over 辺へ戻す。 -/
def roofPointSliceOneSimplexOfTriangle (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a) _⦋0⦌) (G : Δ[2] ⟶ X)
    (h₀ : stdSimplex.δ (0 : Fin 3) ≫ G =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge a v).edge) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a) _⦋1⦌ :=
  ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).hom ≫ G, by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinStdSimplexIso_rightPoint_inr]
    have he : SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.lastVertex 1) =
        stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3) := by
      change SSet.stdSimplex.map _ = SSet.stdSimplex.map _ ≫ SSet.stdSimplex.map _
      rw [← CategoryTheory.Functor.map_comp]
      congr 1
      decide
    rw [he, Category.assoc, h₀]
    exact roofPointSliceVertexEdge_fixed a v⟩

/-- 三角形から戻した実 over 辺は、元の三角形全体を厳密に回収する。 -/
lemma roofPointSliceOneSimplexOfTriangle_triangle (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a) _⦋0⦌)
    (G : Δ[2] ⟶ X) (h₀ : stdSimplex.δ (0 : Fin 3) ≫ G =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge a v).edge) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle a (roofPointSliceOneSimplexOfTriangle a v G h₀) = G := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).inv ≫ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).hom ≫ G) = G
  rw [Iso.inv_hom_id_assoc]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
