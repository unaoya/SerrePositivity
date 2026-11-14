module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGWalkingHom

/-! # 自由 Hom 係数の元の dg 圏への評価

概要：係数複体から元の Hom への任意の鎖写像を dg 関手へ拡張する。
方針：対象二つと生成辺の像を既存の自由 dg 圏の lift に渡す。
規約：Hom の全次数を保つ。使われ方：元の係数と閉前合成した係数の一斉評価。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 自由 Hom の二対象を、元の指定二対象へ送る。 -/
def dgWalkingHomEvaluationObject (q y : D) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGWalkingHomVertex.{v} → D
  | ⟨false⟩ => q
  | ⟨true⟩ => y

/-- 指定鎖写像は唯一の生成辺を評価し、他の零複体上の辺は零へ送る。 -/
def dgWalkingHomEvaluationEdge (M : Complex A) (q y : D) (φ : M ⟶ homObject A D q y) :
    ∀ a b, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomQuiver A M a b ⟶
      homObject A D (dgWalkingHomEvaluationObject D q y a)
        (dgWalkingHomEvaluationObject D q y b)
  | ⟨false⟩, ⟨false⟩ => 0
  | ⟨false⟩, ⟨true⟩ => φ
  | ⟨true⟩, ⟨false⟩ => 0
  | ⟨true⟩, ⟨true⟩ => 0

/-- 任意の係数鎖写像から、その自由 Hom dg 圏上の評価 dg 関手を得る。 -/
def dgWalkingHomEvaluation (M : Complex A) (q y : D) (φ : M ⟶ homObject A D q y) :
    DGFunctor A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGWalkingHom.{u, v} A M) D :=
  FreeDGCategory.lift A _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGWalkingHomVertex D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomQuiver A M)
    (dgWalkingHomEvaluationObject D q y) (dgWalkingHomEvaluationEdge A D M q y φ)

/-- 評価は、元の係数複体上で指定した鎖写像そのもの。 -/
lemma dgWalkingHomEvaluation_generator (M : Complex A) (q y : D)
    (φ : M ⟶ homObject A D q y) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomGenerator A M ≫
      (dgWalkingHomEvaluation A D M q y φ).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomSource A M) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomTarget A M) = φ :=
  FreeDGCategory.lift_edge A _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGWalkingHomVertex D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomQuiver A M)
    (dgWalkingHomEvaluationObject D q y) (dgWalkingHomEvaluationEdge A D M q y φ) _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories
