module

public import SerrePositivity.InfinityCategories.F2.PointConeIdentityComparison
public import SerrePositivity.InfinityCategories.F2.SimplexConeRestriction
public import SerrePositivity.InfinityCategories.F2.FunctorVertexConeReindex

/-!
概要：始点への left anodyne な制限を持つ形状の極限錐を元の脚で判定する。
方針：元の錐を一点に制限し、標準辺への厳密な読み替えと可逆性判定を合成する。
規約：指定された全錐を保持。使われ方：単体形状の coherent filtered 極限交換。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の錐の頂点から指定された形状の一点への標準脚。 -/
def coneInitialLeg {K : SSet.{u}} (a : (Δ[0] : SSet.{u}) ⟶ K) :
    (Δ[1] : SSet.{u}) ⟶ join (Δ[0] : SSet.{u}) K :=
  (joinStdSimplexIso 0 0).inv ≫ joinMap (𝟙 Δ[0]) a

/-- 始点への left anodyne 制限がある形状では、指定脚の可逆性が元の極限性を判定。 -/
lemma isLimitCone_functorVertexCone_iff_initialLeg {K X : SSet.{u}} [Quasicategory X]
    (a : (Δ[0] : SSet.{u}) ⟶ K) [Mono a] (ha : leftAnodyneExtensions a)
    (v : ((ihom (join (Δ[0] : SSet.{u}) K)).obj X) _⦋0⦌) :
    IsLimitCone (functorVertexCone v) ↔
      IsEquivalencePathVertex (((pre (coneInitialLeg a)).app X).app (Opposite.op ⦋0⦌) v) := by
  have he : intervalFunctorVertexEdge
      (((pre (coneInitialLeg a)).app X).app (Opposite.op ⦋0⦌) v) =
      SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫
        (restrictJoinCone (functorVertexCone v) a).val) := by
    unfold intervalFunctorVertexEdge
    rw [functorVertexMap_precomp]
    rfl
  exact (isLimitCone_restrict_iff_of_leftAnodyne (functorVertexCone v) a ha).symm.trans
    ((isLimitCone_point_iff_edge _).trans (isInvertibleEdge_congr he.symm))

end SerrePositivity.InfinityCategories.F2
