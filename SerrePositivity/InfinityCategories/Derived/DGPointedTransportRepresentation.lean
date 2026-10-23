module
public import SerrePositivity.InfinityCategories.Derived.DGFiberTransportSquare
public import SerrePositivity.InfinityCategories.F1.Transport.SquareRepresentation
/-!
概要：同じ実 pointed 表示と全 fiber 同値から、同じ全空間を分類する実 transport 表現を作る。
方針：F1 の実四角形の fiber 射を元の直接 fiber 射へ同定し、同じ二つの射を保持する。
規約：各点の同値だけから全関手同型を結論しない。使われ方：二つの実 Hom 表示の分類比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits SSet
open scoped Simplicial
attribute [local instance] vertexFiber_kanComplex_of_leftFibration
/-- F1 の同じ実四角形の fiber 射は、元の直接 fiber 射そのもの。 -/
lemma dgLeftTransportSquare_fiber_eq {E B : SSet.{u + 1}} {p : E ⟶ B}
    (S : LeftTransportSquare p) (b : B _⦋0⦌) :
    S.pointedFiberMap b =
      transportSquareFiberMap p pointedSpaceProjection S.pointedMap S.diagram S.comm b := by
  apply vertexFiber_hom_ext pointedSpaceProjection (S.diagram.app _ b)
  rw [LeftTransportSquare.pointedFiberMap_ι, transportSquareFiberMap_ι]
/-- 同じ実 pointed 表示とその全 fiber 同値から作る、元の射影の実 transport 表現。 -/
def dgPointedTransportRepresentation {E B : SSet.{u + 1}} (p : E ⟶ B) [LeftFibration p]
    (G : B ⟶ SpaceInfinity.{u}) (a : E ⟶ PointedSpaceInfinity.{u})
    (h : a ≫ pointedSpaceProjection = p ≫ G)
    (he : ∀ b, IsQCatEquivalence (transportSquareFiberMap p pointedSpaceProjection a G h b)) :
    LeftTransportRepresentation p :=
  LeftTransportSquare.toRepresentation {diagram := G, pointedMap := a, comm := h} (by
    intro b
    rw [dgLeftTransportSquare_fiber_eq]
    exact he b)
/-- 同じ実表現の分類図式は、元の同じ全空間値関手。 -/
lemma dgPointedTransportRepresentation_diagram {E B : SSet.{u + 1}}
    (p : E ⟶ B) [LeftFibration p] (G : B ⟶ SpaceInfinity.{u})
    (a : E ⟶ PointedSpaceInfinity.{u}) (h : a ≫ pointedSpaceProjection = p ≫ G)
    (he : ∀ b, IsQCatEquivalence (transportSquareFiberMap p pointedSpaceProjection a G h b)) :
    (dgPointedTransportRepresentation p G a h he).diagram = G := rfl
/-- 同じ実表現の全空間側の写像も、元の同じ pointed 表示そのもの。 -/
lemma dgPointedTransportRepresentation_pointedMap {E B : SSet.{u + 1}}
    (p : E ⟶ B) [LeftFibration p] (G : B ⟶ SpaceInfinity.{u})
    (a : E ⟶ PointedSpaceInfinity.{u}) (h : a ≫ pointedSpaceProjection = p ≫ G)
    (he : ∀ b, IsQCatEquivalence (transportSquareFiberMap p pointedSpaceProjection a G h b)) :
    (dgPointedTransportRepresentation p G a h he).pointedMap = a := by
  change pullback.lift a p h ≫ pullback.fst pointedSpaceProjection G = a
  exact pullback.lift_fst _ _ _
end SerrePositivity.InfinityCategories
