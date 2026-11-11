module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ModelUnitSixTriangleBoundary
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.FunctorEdgeHomotopyRecovery
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)

def dgGluingModelRightUnitLoop : SSet.Homotopy
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedFirstCompositionDiagonal R C D M X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedFirstCompositionDiagonal R C D M X Y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelUnitSixTriangleDiagram R C D M X Y).edge 0 0)

def dgGluingModelLeftUnitLoop : SSet.Homotopy
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedLastCompositionDiagonal R C D M X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedLastCompositionDiagonal R C D M X Y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelUnitSixTriangleDiagram R C D M X Y).edge 2 2)

lemma dgGluingModelRightUnitLoop_edge :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (dgGluingModelRightUnitLoop R C D M X Y) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelUnitSixTriangleDiagram R C D M X Y).edge 0 0 :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFunctorEdge_homotopy_recovery _

lemma dgGluingModelLeftUnitLoop_edge :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (dgGluingModelLeftUnitLoop R C D M X Y) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelUnitSixTriangleDiagram R C D M X Y).edge 2 2 :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFunctorEdge_homotopy_recovery _
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
