module

public import SerrePositivity.InfinityCategories.F2.Compact.ColimitRepresentableCone
public import SerrePositivity.InfinityCategories.F1.PreFiberKan

/-!
概要：元の余極限からの全 Hom の極限錐を、同じ全パラメーター図式へ制限する。
方針：前合成後の評価を元の同じ頂点の評価へ戻し、各点の極限性を保つ。
規約：パラメーターの全単体・元の余錐・元の全共変 Hom を同時に保持する。
使われ方：κ-filtered 図式への制限と有限極限・余極限交換との接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact
variable {K C : SSet.{u}} [Quasicategory C] {D : K ⟶ C}

/-- 元の全 Hom 極限錐を、全パラメーターの同じ図式へ制限する。 -/
def colimitRepresentableRestriction {A : SSet.{u + 1}} (c : JoinCocone D)
    (f : A ⟶ (SSet.uliftFunctor.{u + 1, u}).obj C) :=
  mapJoinCone ((pre f).app SpaceInfinity.{u}) (colimitRepresentableCone c)

/-- 制限後の頂点も、元の余極限頂点からの同じ全 Hom 関手への前合成そのもの。 -/
lemma colimitRepresentableRestriction_vertex {A : SSet.{u + 1}} (c : JoinCocone D)
    (f : A ⟶ (SSet.uliftFunctor.{u + 1, u}).obj C) :
    (colimitRepresentableRestriction c f).vertex =
      functorVertex (f ≫ covariantRepresentableInfinity c.vertex) := by
  rw [colimitRepresentableRestriction, mapJoinCone_vertex, colimitRepresentableCone_vertex]
  rfl

/-- 元の任意の全パラメーター図式への制限後も、同じ全 Hom 錐は各点極限。 -/
lemma colimitRepresentableRestriction_isPointwiseLimit {A : SSet.{u + 1}}
    (c : JoinCocone D) (hc : IsColimitCone c)
    (f : A ⟶ (SSet.uliftFunctor.{u + 1, u}).obj C) :
    IsPointwiseLimitCone (colimitRepresentableRestriction c f) := by
  intro a
  change IsLimitCone (mapJoinCone (((pre f).app SpaceInfinity.{u}) ≫ evaluateFunctorAt a)
    (colimitRepresentableCone c))
  rw [evaluateFunctorAt_pre]
  exact colimitRepresentableCone_isPointwiseLimit c hc (f.app _ a)

/-- 元の全パラメーター図式への制限は、元の関手圏の極限錐を実際に与える。 -/
lemma colimitRepresentableRestriction_isLimit {A : SSet.{u + 1}}
    (c : JoinCocone D) (hc : IsColimitCone c)
    (f : A ⟶ (SSet.uliftFunctor.{u + 1, u}).obj C) :
    IsLimitCone (colimitRepresentableRestriction c f) :=
  isLimitCone_of_pointwise _ (colimitRepresentableRestriction_isPointwiseLimit c hc f)

end SerrePositivity.InfinityCategories.F2.Compact
