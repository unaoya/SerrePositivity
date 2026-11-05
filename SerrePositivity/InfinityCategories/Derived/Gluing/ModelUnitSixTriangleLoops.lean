module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ModelUnitSixTriangleBoundary
public import SerrePositivity.InfinityCategories.Derived.Gluing.FunctorEdgeHomotopyRecovery
/-! # 実六片の二つの単位辺を同じ実閉路へ戻す

概要：六片の二つの単位辺を、同じ辺の代表と全円柱写像を持つ実閉路として保持する。
方針：関手辺を uncurry し、辺の回収則で指定境界への入力を合わせる。
規約：主係数対角の二端で閉路を取り、代表を選び直さない。
使われ方：単位面の退化・相対四面体比較から④の指定境界充填へ進む。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded DGNerve SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)

def dgGluingModelRightUnitLoop : SSet.Homotopy
    (dgGluingHomDerivedFirstCompositionDiagonal R C D M X Y)
    (dgGluingHomDerivedFirstCompositionDiagonal R C D M X Y) :=
  simplicialHomotopyOfFunctorEdge ((dgGluingModelUnitSixTriangleDiagram R C D M X Y).edge 0 0)

def dgGluingModelLeftUnitLoop : SSet.Homotopy
    (dgGluingHomDerivedLastCompositionDiagonal R C D M X Y)
    (dgGluingHomDerivedLastCompositionDiagonal R C D M X Y) :=
  simplicialHomotopyOfFunctorEdge ((dgGluingModelUnitSixTriangleDiagram R C D M X Y).edge 2 2)

lemma dgGluingModelRightUnitLoop_edge :
    functorEdgeOfSimplicialHomotopy (dgGluingModelRightUnitLoop R C D M X Y) =
      (dgGluingModelUnitSixTriangleDiagram R C D M X Y).edge 0 0 :=
  dgGluingFunctorEdge_homotopy_recovery _

lemma dgGluingModelLeftUnitLoop_edge :
    functorEdgeOfSimplicialHomotopy (dgGluingModelLeftUnitLoop R C D M X Y) =
      (dgGluingModelUnitSixTriangleDiagram R C D M X Y).edge 2 2 :=
  dgGluingFunctorEdge_homotopy_recovery _
end SerrePositivity.InfinityCategories
