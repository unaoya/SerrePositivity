module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitRawLastLongInverseFactorization
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitIntervalModelRawLastCancellation

/-!
概要：元の模型三角形式の新長辺残余を、同じ元の二指定逆比較の単位・値への像へ分解する。
方針：元の模型残余の実端点補正と、任意の前後合成で保つ長辺分解を合成する。
規約：元の模型残余・単位・値を保持。使われ方：元の模型三角形の全区間族の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d)
local notation "u₀" => Subtype.val (leftUnstraighteningMappingVertexMap F
  (SSet.const (JoinCocone.vertex (coherentDiagramTotalCocone F)))
  (coconeTransformationVertex (coherentDiagramTotalCocone F)))
local notation "V" => pointedFiberValueTo (coherentDiagramTotalCocone_vertex J)
local notation "P" => coherentColimitRawConstantFiberProjection B F

/-- 元の模型残余は、元の普遍三角形と第一辺指定比較の逆の同じ元の単位・値への像。 -/
lemma coherentColimitIntervalModelRawLastRemainder_heq_factorization :
    HEq (coherentColimitIntervalModelRawLastRemainder B T)
      ((((coherentColimitRawUniversalTriangleComparison B T P).precomp u₀).postcomp V).symm ≪≫
        ((((coherentColimitConstantTransportRawPointIso B a).postcomp
          (coherentColimitRawFiberTransport B b)).precomp u₀).postcomp V).symm) := by
  exact (vertexIsoOfEq_heq _ _ _).trans
    (coherentColimitRawLastLong_inverse_factorization_precomp_postcomp B T u₀ V)

end SerrePositivity.InfinityCategories.F2
