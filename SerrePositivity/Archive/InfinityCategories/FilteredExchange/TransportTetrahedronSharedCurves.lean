module

public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.TransportTetrahedronSharedEdges
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.TransportTriangleBaseAccess

/-!
概要：四面体の六本の実共有辺は、同じ元の底の区間族を持つ。
方針：元の実辺の射影と区間表示の単射性を使う。
規約：底の族を仮定で同一視しない。使われ方：四面の比較の型を揃える。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E B P : SSet.{u}} {p : E ⟶ B} {v : Fin 4 → B _⦋0⦌}
  {f : ∀ i, P ⟶ vertexFiber p (v i)} (D : TransportTetrahedronDiagram p v f)

/-- 実辺 01 の底の区間族は両面で同じ。 -/
lemma TransportTetrahedronDiagram.shared_curve01 :
    (D.face 2).base.bottom = (D.face 3).base.bottom := by
  apply intervalMappingUncurry_injective
  exact ((D.face 2).diagram.bottomPrism_projection).symm.trans
    ((congrArg (fun V => V ≫ p) D.shared_edge01).trans
      (D.face 3).diagram.bottomPrism_projection)

/-- 実辺 02 の底の区間族は両面で同じ。 -/
lemma TransportTetrahedronDiagram.shared_curve02 :
    (D.face 1).base.bottom = (D.face 3).base.left := by
  apply intervalMappingUncurry_injective
  exact ((D.face 1).diagram.bottomPrism_projection).symm.trans
    ((congrArg (fun V => V ≫ p) D.shared_edge02).trans
      (D.face 3).diagram.leftPrism_projection)

/-- 実辺 03 の底の区間族は両面で同じ。 -/
lemma TransportTetrahedronDiagram.shared_curve03 :
    (D.face 1).base.left = (D.face 2).base.left := by
  apply intervalMappingUncurry_injective
  exact ((D.face 1).diagram.leftPrism_projection).symm.trans
    ((congrArg (fun V => V ≫ p) D.shared_edge03).trans
      (D.face 2).diagram.leftPrism_projection)

/-- 実辺 12 の底の区間族は両面で同じ。 -/
lemma TransportTetrahedronDiagram.shared_curve12 :
    (D.face 0).base.bottom = (D.face 3).base.right := by
  apply intervalMappingUncurry_injective
  exact ((D.face 0).diagram.bottomPrism_projection).symm.trans
    ((congrArg (fun V => V ≫ p) D.shared_edge12).trans
      (D.face 3).diagram.rightPrism_projection)

/-- 実辺 13 の底の区間族は両面で同じ。 -/
lemma TransportTetrahedronDiagram.shared_curve13 :
    (D.face 0).base.left = (D.face 2).base.right := by
  apply intervalMappingUncurry_injective
  exact ((D.face 0).diagram.leftPrism_projection).symm.trans
    ((congrArg (fun V => V ≫ p) D.shared_edge13).trans
      (D.face 2).diagram.rightPrism_projection)

/-- 実辺 23 の底の区間族は両面で同じ。 -/
lemma TransportTetrahedronDiagram.shared_curve23 :
    (D.face 0).base.right = (D.face 1).base.right := by
  apply intervalMappingUncurry_injective
  exact ((D.face 0).diagram.rightPrism_projection).symm.trans
    ((congrArg (fun V => V ≫ p) D.shared_edge23).trans
      (D.face 1).diagram.rightPrism_projection)

end SerrePositivity.InfinityCategories.F2
