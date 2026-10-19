module
public import SerrePositivity.InfinityCategories.Derived.DGLastHornSolution
public import SerrePositivity.InfinityCategories.Derived.DGVerdierDiagramEdgeHorn

/-! # 指定実図式辺の Q・A の解から共通始錐の一次整合性へ

概要：実分母図式の各指定辺から回収した二つの微分式の解を、実 over 内の整合性二単体へ戻す。
方針：元の dg nerve の指定ホーンを Q・A で延長し、同じ三辺の全部分複体へ回収する。
規約：元の図式辺と二脚を厳密に保持。解や追加細分の存在をこの定義の仮定と混同しない。
使われ方：有限分母消去の代数的解の受入界面。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {P : Set D} {x : D} {K : SSet.{max u v}}
variable {f : K ⟶ (dgVerdierOver A D P x : SSet.{max u v})}
variable (C : DGVerdierDiagramVertexCone A D P x f) (e : K _⦋1⦌)

/-- 実図式辺から回収した Q・A の解は、同じ実図式辺と二脚の合成二単体を与える。 -/
def dgVerdierDiagramEdgeCompStructOfCochains
    (S : DGLastHornSolution (dgVerdierDiagramEdgeHorn A D C e)) :
    Truncated.Edge.CompStruct (C.leg (K.δ 1 e))
      ((edgeOfSimplex e).map ((truncation 2).map f)) (C.leg (K.δ 0 e)) :=
  dgVerdierDiagramEdgeCompStructOfFiller A D C e S.extension S.fac

end SerrePositivity.InfinityCategories
