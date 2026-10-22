module

public import SerrePositivity.InfinityCategories.F2.FunctorTriangleSourceFiberMap
public import SerrePositivity.InfinityCategories.F2.CoherentColimitConstantTriangleFiberValue
public import SerrePositivity.InfinityCategories.F2.PointedFiberValueTo

/-!
概要：五因子式の定値三角形を、下側因子と同じ固定 native 値への fiber 像に戻す。
方針：元の実単位頂点で評価し、任意の fiber 射への同じ全三角形の像を使う。
規約：元の比較と指定頂点等式を保持。使われ方：定値三角形と下側輸送の因子消去。
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
local notation "v₀" => leftUnstraighteningMappingVertexMap F (SSet.const z₀)
  (coherentVertexOfHomotopy u₀)
local notation "V" => pointedFiberValueTo (coherentDiagramTotalCocone_vertex J)
local notation "Q" => constantTargetValueProjectionTo p (coherentDiagramTotalCocone_vertex J)

/-- 元の定値三角形因子は、同じ fiber 比較を元の単位と固定値の射で写したもの。 -/
lemma coherentColimitConstantTriangleValueTo_heq_fiber_unit :
    HEq (VertexIso.map
      ((functorTriangleSequentialPostComparison (coherentColimitConstantTriangle B T) p).app
        ((functorHomotopyRelativePost u₀ p).app _ x₀)) Q)
      (((coherentColimitConstantTriangleFiberIso B T).precomp (Subtype.val v₀)).postcomp V) := by
  have hx : (functorHomotopyRelativePost u₀ p).app _ x₀ =
      relativeFunctorVertex (leftUnstraighteningProjection (SSet.const z₀)) p
        (Subtype.val v₀) (Subtype.property v₀) := by
    apply Subtype.ext
    rfl
  rw [constantTargetValueProjectionTo_eq_fiberValueTo, hx]
  refine (functorTriangleSequentialPostComparison_source_fiberMap_heq_over_base
    (coherentColimitConstantTriangle B T) (Subtype.val v₀) V p (Subtype.property v₀)).trans ?_
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
    (constantUnstraighteningFiberProjection ((SSet.uliftFunctor.{u + 1, u}).obj B) z₃)
      (Subtype.val v₀) V).symm

end SerrePositivity.InfinityCategories.F2
