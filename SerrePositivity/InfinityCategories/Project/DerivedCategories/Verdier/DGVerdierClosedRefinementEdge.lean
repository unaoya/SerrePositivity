module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.DGClosedRoofRefinements
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.DGStrictRoofEdges

/-! # 元の指定閉細分の実 Verdier over 辺

概要：元の閉分母間の射を、指定二頂点と指定始域辺を持つ実分母辺にする。
方針：通常の閉分母圏の nerve 辺を写し、既存の全射影公式を評価する。
規約：閉細分射を選び直さない。使われ方：全係数の実屋根 prism の底の指定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet CartesianMonoidalCategory
open scoped _root_.Simplicial

/-- 係数を忘れた辺の族は、零端点で指定始点に定値。 -/
lemma roofEdgeCylinder_zero {K X : SSet.{u}} {a b : X _⦋0⦌} (e : X.Edge a b) :
    SSet.ι₀ ≫ (snd K Δ[1] ≫ SSet.yonedaEquiv.symm e.edge) = SSet.const a := by
  rw [← Category.assoc, SSet.ι₀_snd, SSet.const_comp]
  apply congrArg SSet.const
  rw [SSet.yonedaEquiv_symm_app]
  have h : SSet.stdSimplex.objEquiv.{u}
      (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = SimplexCategory.δ (1 : Fin 2) := by decide
  rw [h]
  exact e.src_eq

/-- 係数を忘れた辺の族は、一端点で指定終点に定値。 -/
lemma roofEdgeCylinder_one {K X : SSet.{u}} {a b : X _⦋0⦌} (e : X.Edge a b) :
    SSet.ι₁ ≫ (snd K Δ[1] ≫ SSet.yonedaEquiv.symm e.edge) = SSet.const b := by
  rw [← Category.assoc, SSet.ι₁_snd, SSet.const_comp]
  apply congrArg SSet.const
  rw [SSet.yonedaEquiv_symm_app]
  have h : SSet.stdSimplex.objEquiv.{u}
      (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = SimplexCategory.δ (0 : Fin 2) := by decide
  rw [h]
  exact e.tgt_eq

variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 元の指定閉細分を、元の指定二分母を両端とする実 over 辺として読む。 -/
def dgClosedVerdierDenominatorEdge (P : Set D) (x : D)
    {s t : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x} (r : s ⟶ t) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).Edge
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominatorVertex A D P x s)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominatorVertex A D P x t) :=
  let e := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofNerveEdge r).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofVerdierMap A D P x)
  SSet.Edge.mk e.edge (e.src_eq.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofVerdierMap_vertex A D P x s))
    (e.tgt_eq.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofVerdierMap_vertex A D P x t))

/-- 指定実分母辺の始域射影は、元の指定閉細分の実辺。 -/
lemma dgClosedVerdierDenominatorEdge_source (P : Set D) (x : D)
    {s t : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x} (r : s ⟶ t) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource A D P x).app (Opposite.op ⦋1⦌)
      (dgClosedVerdierDenominatorEdge A D P x r).edge = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D r.hom.left).edge :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofVerdierMap_edge_source A D P x r

end SerrePositivity.InfinityCategories.Project.DerivedCategories
