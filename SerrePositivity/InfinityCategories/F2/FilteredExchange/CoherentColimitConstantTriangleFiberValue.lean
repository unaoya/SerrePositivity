module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitConstantTriangleValue
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitConstantTriangleFiberIso
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorIsoPrecompPostcompAssociation

/-!
概要：元の値の整合式の定値三角形因子を、因子消去に使う同じ fiber 比較へ戻す。
方針：元の単位での前合成と元の値への後合成を同じ指定三角形比較に適用する。
規約：元の五因子の指定値を保持。使われ方：下側輸送比較の消去の値への接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {c : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b c)
local notation "p" => leftUnstraighteningProjection F
local notation "z₀" => JoinCocone.vertex (coherentDiagramTotalCocone F)
local notation "z₁" => JoinCocone.vertex (coherentDiagramTotalCocone G)
local notation "z₃" => JoinCocone.vertex (coherentDiagramTotalCocone J)
local notation "u₀" => coconeTransformationHomotopy (coherentDiagramTotalCocone F)
local notation "x₀" => relativeFunctorVertex p p (𝟙 (leftUnstraightening F)) (Category.id_comp p)
local notation "v₀" => Subtype.val (leftUnstraighteningMappingVertexMap F
  (SSet.const (JoinCocone.vertex (coherentDiagramTotalCocone F))) (coherentVertexOfHomotopy u₀))
local notation "V" => QCatEquivalence.hom (pointedSpaceFiberValueEquivalence z₃)

/-- 元の五因子の定値三角形因子は、因子消去の同じ fiber 比較の元の単位と値への像。 -/
lemma coherentColimitConstantTriangleValue_heq_fiber_unit :
    HEq (VertexIso.map
      ((functorTriangleSequentialPostComparison (coherentColimitConstantTriangle B T) p).app
        ((functorHomotopyRelativePost u₀ p).app _ x₀))
      ((constantUnstraighteningRelativeIso p z₃).hom ≫ (ihom (leftUnstraightening F)).map V))
      (((coherentColimitConstantTriangleFiberIso B T).precomp v₀).postcomp V) := by
  refine (coherentColimitConstantTriangleValue_heq_total B T).trans ?_
  let W := coherentTriangleOfFunctorTriangle (coherentColimitConstantTriangle B T)
  let e := unstraighteningTriangleVertexIso
    (SSet.const z₀ : ((SSet.uliftFunctor.{u + 1, u}).obj B) ⟶ SpaceInfinity)
    (SSet.const z₁) (SSet.const z₃)
    (coherentVertexOfHomotopy
      (simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B a)))
    (coherentVertexOfHomotopy
      (simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B b)))
    (coherentVertexOfHomotopy
      (simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B c)))
    W.diagram W.first W.second W.long
  exact (functorIso_postcomp_precomp_postcomp_heq e
    (constantUnstraighteningFiberProjection ((SSet.uliftFunctor.{u + 1, u}).obj B) z₃) v₀ V).symm

end SerrePositivity.InfinityCategories.F2
