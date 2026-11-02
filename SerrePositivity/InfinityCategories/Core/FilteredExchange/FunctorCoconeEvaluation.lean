module

public import SerrePositivity.InfinityCategories.Core.Cocone
public import SerrePositivity.InfinityCategories.Core.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Core.FunctorLimits
public import SerrePositivity.InfinityCategories.Stable.TrivialFibrationCocone

/-!
概要：関手単体集合の元の余錐を各点で評価し、点ごとの余極限性を表す。
方針：元の余錐を評価射で後合成する。
規約：余錐全体と高次の整合を保持。使われ方：一般 coherent filtered 図式の極限交換。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 関手単体集合の元の余錐を一つの指定頂点で評価する。 -/
def evaluateFunctorCocone {J K X : SSet.{u}} {p : J ⟶ (ihom K).obj X}
    (c : JoinCocone p) (k : K _⦋0⦌) : JoinCocone (evaluateFunctorDiagram p k) :=
  mapJoinCocone (evaluateFunctorAt k) c

/-- 点ごとの余極限性は同じ元の余錐の全ての評価の余極限性である。 -/
def IsPointwiseColimitCone {J K X : SSet.{u}} {p : J ⟶ (ihom K).obj X}
    (c : JoinCocone p) : Prop := ∀ k : K _⦋0⦌, IsColimitCone (evaluateFunctorCocone c k)

/-- 評価後の頂点は元の余錐の頂点を同じ点で評価したもの。 -/
lemma evaluateFunctorCocone_vertex {J K X : SSet.{u}} {p : J ⟶ (ihom K).obj X}
    (c : JoinCocone p) (k : K _⦋0⦌) :
    (evaluateFunctorCocone c k).vertex =
      (evaluateFunctorAt k).app (Opposite.op ⦋0⦌) c.vertex := by
  rfl

end SerrePositivity.InfinityCategories.F2
