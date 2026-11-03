module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitConstantTriangleValueToEndpoint
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitValueProjectionEndpoints

/-!
概要：五因子式の元の定値三角形因子を、下側輸送因子の逆と厳密に消去する。
方針：元の因子の両実端点と値を同じ fiber 比較へ戻し、同じ消去式を適用する。
規約：元の全式の因子を保持。使われ方：a6 の模型五因子式の整合の回収。
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
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d)
local notation "p" => leftUnstraighteningProjection F
local notation "c₀" => coherentDiagramTotalCocone F
local notation "uF" => coconeTransformationHomotopy (coherentDiagramTotalCocone F)
local notation "x₀" => relativeFunctorVertex p p (𝟙 (leftUnstraightening F)) (Category.id_comp p)
local notation "Q" => constantTargetValueProjectionTo p (coherentDiagramTotalCocone_vertex J)
local notation "V" => pointedFiberValueTo (coherentDiagramTotalCocone_vertex J)
local notation "u₀" => Subtype.val (leftUnstraighteningMappingVertexMap F
  (SSet.const (JoinCocone.vertex c₀)) (coconeTransformationVertex c₀))
local notation "e" => VertexIso.map
  (FunctorIso.app (functorTriangleSequentialPostComparison (coherentColimitConstantTriangle B T) p)
    (NatTrans.app (functorHomotopyRelativePost uF p) (Opposite.op ⦋0⦌) x₀)) Q

/-- 五因子の元の三角形因子を実両端で戻すと、同じ fiber 三角形の指定値に等しい。 -/
lemma coherentColimitConstantTriangleProjectionTo_eq_fiber :
    vertexIsoOfEq e (coherentColimitValueProjection_lower_vertex B d)
      (coherentColimitConstantTriangleValueTo_target_vertex B (a := a) (b := b)) =
    vertexIsoOfEq (((coherentColimitConstantTriangleFiberIso B T).precomp u₀).postcomp V)
      (coherentColimitLowerPoint_source_valueTo_vertex B d) rfl := by
  have h := coherentColimitConstantTriangleValueTo_heq_fiber_unit B T
  rw [coherentVertexOfHomotopy_cocone] at h
  exact eq_of_heq ((vertexIsoOfEq_heq _ _ _).trans
    (h.trans (vertexIsoOfEq_heq _ _ _).symm))

/-- 元の五因子式の実三角形因子も、同じ下側因子の逆と元の残りの比較へ消去される。 -/
lemma coherentColimitConstantTriangleProjectionTo_lower_cancel :
    (coherentColimitLowerTransportFactorIso B d).symm ≪≫
      vertexIsoOfEq e (coherentColimitValueProjection_lower_vertex B d)
        (coherentColimitConstantTriangleValueTo_target_vertex B (a := a) (b := b)) =
    vertexIsoOfEq
      ((((coherentColimitConstantTriangleRemainderIso B T).precomp u₀).postcomp V).symm)
      (coherentColimitLowerPoint_target_valueTo_vertex B d) rfl := by
  rw [coherentColimitConstantTriangleProjectionTo_eq_fiber]
  exact coherentColimitLowerValueTo_triangle_cancel B T

end SerrePositivity.InfinityCategories.F2
