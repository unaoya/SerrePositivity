module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierDiagramVertexCone
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierConeEdgeBoundary

/-! # 実分母図式の各辺に沿う始錐の一次整合性ホーン

概要：図式と頂点上の始錐から、各指定図式辺を固定した具体的な三次外ホーンを得る。
方針：図式辺を実分母圏へ写し、始点・終点の脚と合わせて元の dg nerve へ移す。
規約：退化辺を含む任意の図式一単体に定義。使われ方：追加分母後の一次整合性の充填。
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
variable {P : Set D} {x : D} {K : SSet.{max u v}}
variable {f : K ⟶ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet.{max u v})}
variable (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierDiagramVertexCone A D P x f) (e : K _⦋1⦌)

/-- 指定図式辺と両端の脚に対する元の dg nerve の整合性ホーン。 -/
def dgVerdierDiagramEdgeHorn : (Λ[3, 3] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierConeEdgeHorn A D P x (C.leg (K.δ 1 e))
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex e).map ((truncation 2).map f)) (C.leg (K.δ 0 e))

/-- 図式辺に対応する三次ホーンの充填は、同じ辺と同じ二脚の実整合性を与える。 -/
def dgVerdierDiagramEdgeCompStructOfFiller (F : Δ[3] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (hF : (horn 3 3).ι ≫ F = dgVerdierDiagramEdgeHorn A D C e) :
    Truncated.Edge.CompStruct (C.leg (K.δ 1 e))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex e).map ((truncation 2).map f)) (C.leg (K.δ 0 e)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierConeEdgeCompStructOfFiller A D P x (C.leg (K.δ 1 e))
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex e).map ((truncation 2).map f)) (C.leg (K.δ 0 e)) F hF

end SerrePositivity.InfinityCategories.Project.DerivedCategories
