module

public import SerrePositivity.InfinityCategories.F2.Compact.TerminalBoundaryReflection
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.FunctorVertexCone
public import SerrePositivity.InfinityCategories.Core.FunctorPointwiseLimitCriterion

/-!
概要：元の二つの極限錐の比較辺は、底の全図式への制限が可逆なら全体で可逆。
方針：元の各極限錐の相対終点境界充填と Hom の反映を使う。
規約：元の全錐と同じ実際の辺を保持。使われ方：点ごとの余極限補完と指定全錐の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact

/-- 元の関手頂点が表す極限錐は、同じ全底図式への制限について相対終点。 -/
lemma limitConeVertex_terminalBoundary {K X : SSet.{u}} [Quasicategory X]
    (a : ((ihom (join (Δ[0] : SSet.{u}) K)).obj X) _⦋0⦌)
    (ha : IsLimitCone (functorVertexCone a)) : TerminalBoundaryLifting (coneRestriction K X) a := by
  have h := terminalBoundaryLifting_coneRestriction_of_isLimitCone (functorVertexCone a) ha
  have he : functorVertex (functorVertexCone a).val = a :=
    (functorVertexEquiv _ _).apply_symm_apply a
  rwa [he] at h

/-- 元の極限錐の全比較の可逆性は、元の底図式への同じ比較から反映できる。 -/
lemma limitConeEdge_reflects_invertible {K X : SSet.{u}} [Quasicategory X]
    {a b : ((ihom (join (Δ[0] : SSet.{u}) K)).obj X) _⦋0⦌}
    (ha : IsLimitCone (functorVertexCone a)) (hb : IsLimitCone (functorVertexCone b))
    (e : ((ihom (join (Δ[0] : SSet.{u}) K)).obj X).Edge a b)
    (he : IsInvertibleEdge (e.map (coneRestriction K X))) : IsInvertibleEdge e :=
  terminalBoundary_reflects_invertibleEdge (coneRestriction K X)
    (limitConeVertex_terminalBoundary a ha) (limitConeVertex_terminalBoundary b hb) e he

end SerrePositivity.InfinityCategories.F2.Compact
