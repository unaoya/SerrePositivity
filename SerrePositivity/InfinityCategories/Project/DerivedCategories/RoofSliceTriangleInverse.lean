module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofSliceTriangle
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedSlice

/-! # 指定合成三角形から実 over 辺を構成する

概要：二つの実 over 頂点の指定分母を結ぶ合成三角形を、元の端点を保つ実 over 辺へ戻す。
方針：二単体を点との join に移し、既存の三面抽出公式で両端と始域射影を回収する。
規約：厳密閉 over の可換三角形は要求しない。使われ方：実分母の有限共通始錐の脚。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
open scoped _root_.Simplicial
variable {X : SSet.{u}} (a : Δ[0] ⟶ X) (s t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a) _⦋0⦌)
variable (r : Truncated.Edge (X := (truncation 2).obj X)
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection a).app (Opposite.op ⦋0⦌) s)
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection a).app (Opposite.op ⦋0⦌) t))
variable (h : Truncated.Edge.CompStruct r (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge a t)
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge a s))

/-- 点との join へ移した指定合成三角形は、終点の点図式を厳密に固定する。 -/
def roofPointSliceSimplexOfCompStruct : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a) _⦋1⦌ :=
  ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).hom ≫ (SSet.yonedaEquiv (X := X)).symm h.simplex, by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinStdSimplexIso_rightPoint_inr]
    have he : SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.lastVertex 1) =
        SSet.stdSimplex.δ (0 : Fin 2) ≫ SSet.stdSimplex.δ (0 : Fin 3) := by
      change SSet.stdSimplex.map _ = SSet.stdSimplex.map _ ≫ SSet.stdSimplex.map _
      rw [← CategoryTheory.Functor.map_comp]
      congr 1
      decide
    rw [he, Category.assoc, SSet.stdSimplex.δ_comp_yonedaEquiv_symm,
      SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    apply (SSet.yonedaEquiv (X := X)).injective
    rw [Equiv.apply_symm_apply]
    exact (congrArg (fun e : X _⦋1⦌ => X.δ 0 e)
      (show X.δ 0 h.simplex = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge a t).edge from h.d₀)).trans
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge a t).tgt_eq⟩

/-- 実 over 辺から回収する三角形は、入力の指定三角形そのもの。 -/
lemma roofPointSliceSimplexOfCompStruct_triangle :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle a (roofPointSliceSimplexOfCompStruct a s t r h) =
      (SSet.yonedaEquiv (X := X)).symm h.simplex := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).inv ≫ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).hom ≫ _) = _
  exact Iso.inv_hom_id_assoc _ _

/-- 指定三角形から作った実 over 辺の始端は元の指定頂点。 -/
lemma roofPointSliceSimplexOfCompStruct_source :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a).δ 1 (roofPointSliceSimplexOfCompStruct a s t r h) = s := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge_injective a
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle_leg a _ 1, roofPointSliceSimplexOfCompStruct_triangle]
  exact (SSet.stdSimplex.yonedaEquiv_δ_comp
    ((SSet.yonedaEquiv (X := X)).symm (h.simplex : X _⦋2⦌)) (1 : Fin 3)).trans
      ((congrArg (fun z : X _⦋2⦌ => X.δ (1 : Fin 3) z)
        ((SSet.yonedaEquiv (X := X)).apply_symm_apply _)).trans h.d₁)

/-- 指定三角形から作った実 over 辺の終端は元の指定頂点。 -/
lemma roofPointSliceSimplexOfCompStruct_target :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a).δ 0 (roofPointSliceSimplexOfCompStruct a s t r h) = t := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge_injective a
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle_leg a _ 0, roofPointSliceSimplexOfCompStruct_triangle]
  exact (SSet.stdSimplex.yonedaEquiv_δ_comp
    ((SSet.yonedaEquiv (X := X)).symm (h.simplex : X _⦋2⦌)) (0 : Fin 3)).trans
      ((congrArg (fun z : X _⦋2⦌ => X.δ (0 : Fin 3) z)
        ((SSet.yonedaEquiv (X := X)).apply_symm_apply _)).trans h.d₀)

/-- 実 over 辺の始域射影は入力三角形の第一辺そのもの。 -/
lemma roofPointSliceSimplexOfCompStruct_projection :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection a).app (Opposite.op ⦋1⦌)
      (roofPointSliceSimplexOfCompStruct a s t r h) = r.edge := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle_base a _, roofPointSliceSimplexOfCompStruct_triangle]
  exact (SSet.stdSimplex.yonedaEquiv_δ_comp
    ((SSet.yonedaEquiv (X := X)).symm (h.simplex : X _⦋2⦌)) (2 : Fin 3)).trans
      ((congrArg (fun z : X _⦋2⦌ => X.δ (2 : Fin 3) z)
        ((SSet.yonedaEquiv (X := X)).apply_symm_apply _)).trans h.d₂)

/-- 合成三角形を、元の二頂点を厳密に保つ実 over 辺へ戻す。 -/
def roofPointSliceEdgeOfCompStruct :
    Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a)) s t where
  edge := roofPointSliceSimplexOfCompStruct a s t r h
  src_eq := roofPointSliceSimplexOfCompStruct_source a s t r h
  tgt_eq := roofPointSliceSimplexOfCompStruct_target a s t r h

end SerrePositivity.InfinityCategories.Project.DerivedCategories
