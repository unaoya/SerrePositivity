module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.HornFillers.DGLastHornYonedaResidual
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.HornFillers.DGVerdierLastHornDenominator
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGClosedVerdierDenominators

/-! # 実 Verdier 分母の Yoneda 加群 cone の有限 cell 性

概要：指定された実分母の加群 cone は、同じ指定集合からの導来有限 cell である。
方針：実辺と主導来分母の一致、同じ標準 cone 三角形の trW 判定を使う。
規約：前三角性を要求する。使われ方：実最後外ホーン残差の標的の有限 cell 消去。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 元の実閉分母の Yoneda 加群 cone は、指定集合からの導来有限 cell。 -/
lemma dgYonedaVerdierCone_derivedFiniteCell (P : Set D) {y z : _root_.SerrePositivity.DifferentialGraded.ClosedCategory A D}
    (g : y ⟶ z) (hg : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D g).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P) :
    derivedFiniteCellOver A D P ((moduleToDerived A D).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYonedaClosedCone A D g)) := by
  apply ((_root_.SerrePositivity.DifferentialGraded.derivedFiniteCellOver A D P).trW_iff_of_distinguished
    (_root_.SerrePositivity.DifferentialGraded.moduleDerivedConeTriangle A D ((_root_.SerrePositivity.DifferentialGraded.dgYoneda A D).onClosed.map g))
    (_root_.SerrePositivity.DifferentialGraded.moduleDerivedConeTriangle_distinguished A D _)).mp
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge_mem_iff_derived_trW A D P g).mp hg

/-- 実図式辺のホーン残差の標的 cone は、元の指定集合からの導来有限 cell。 -/
lemma dgVerdierDiagramYonedaCone_derivedFiniteCell (P : Set D) (x : D)
    {K : SSet.{max u v}} {f : K ⟶ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet.{max u v})}
    (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierDiagramVertexCone A D P x f) (a : K _⦋1⦌) :
    _root_.SerrePositivity.DifferentialGraded.derivedFiniteCellOver A D P ((_root_.SerrePositivity.DifferentialGraded.moduleToDerived A D).obj
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornYonedaCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramEdgeHorn A D C a))) :=
  dgYonedaVerdierCone_derivedFiniteCell A D P _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramLastClosed_mem A D P x C a)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
