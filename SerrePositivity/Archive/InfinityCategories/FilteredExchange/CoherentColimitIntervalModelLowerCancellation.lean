module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitIntervalModelFiveFactors
public import
  SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitConstantTriangleProjectionToCancellation
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.VertexIsoEndpointComposition

/-!
概要：a6 の元の模型三角形の五因子式から、下側の外側輸送因子を消去する。
方針：同じ実中間頂点で元の右辺を分け、元の定値三角形との消去式を代入する。
規約：三辺・模型比較・残り二因子を保持。使われ方：指定三角形と全錐比較への反映。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u}) [Quasicategory B]
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
local notation "f₀₁" => Subtype.val (leftUnstraighteningMappingVertexMap F G
  (coherentVertexOfHomotopy a))
local notation "rc" => simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B b)
local notation "e" => VertexIso.map
  (FunctorIso.app (functorTriangleSequentialPostComparison (coherentColimitConstantTriangle B T) p)
    (NatTrans.app (functorHomotopyRelativePost uF p) (Opposite.op ⦋0⦌) x₀)) Q

omit [Quasicategory B] in
/-- 元の五因子式の最後の二因子を、同じ固定値の中でそのまま保持した指定合成。 -/
def coherentColimitUnitRightTailValueTo :=
  VertexIso.map (VertexIso.map (coherentColimitUnitValueComparison B a p x₀)
    (functorHomotopyRelativePost rc p)) Q ≪≫
      coherentColimitUnitValueActionTo B b p
        ((functorHomotopyRelativePost a p).app (Opposite.op ⦋0⦌) x₀)

/-- 元の a6 模型式から下側外側因子が消え、同じ長辺輸送の残りと元の二因子が残る。 -/
lemma coherentColimitIntervalModel_lower_cancel :
    coherentColimitIntervalModelUnitComparison B d ≪≫
      vertexIsoOfEq (coherentTotalTriangleNativeModelComparison T)
        (congrArg functorVertex (coherentColimitNativeModelTarget_eq_unit B d))
        (congrArg functorVertex (coherentTotalTriangleNativeModelTarget_eq_unit a b)) =
    vertexIsoOfEq
      ((((coherentColimitConstantTriangleRemainderIso B T).precomp u₀).postcomp V).symm)
      (coherentColimitLowerPoint_target_valueTo_vertex B d) rfl ≪≫
    vertexIsoOfEq (coherentColimitUnitRightTailValueTo B (a := a) (b := b))
      (coherentColimitConstantTriangleValueTo_target_vertex B (a := a) (b := b))
      (coherentColimitValueProjection_composite_vertex B a b) ≪≫
    (coherentColimitUpperUnitFactorIso B b).precomp f₀₁ := by
  have hs := vertexIsoOfEq_trans e (coherentColimitUnitRightTailValueTo B (a := a) (b := b))
    (coherentColimitValueProjection_lower_vertex B d)
    (coherentColimitConstantTriangleValueTo_target_vertex B (a := a) (b := b))
    (coherentColimitValueProjection_composite_vertex B a b)
  have hc := congrArg (fun k => k ≪≫
    vertexIsoOfEq (coherentColimitUnitRightTailValueTo B (a := a) (b := b))
      (coherentColimitConstantTriangleValueTo_target_vertex B (a := a) (b := b))
      (coherentColimitValueProjection_composite_vertex B a b) ≪≫
        (coherentColimitUpperUnitFactorIso B b).precomp f₀₁)
    (coherentColimitConstantTriangleProjectionTo_lower_cancel B T)
  rw [coherentColimitIntervalModel_five_factors]
  change (coherentColimitLowerTransportFactorIso B d).symm ≪≫
    vertexIsoOfEq (e ≪≫ coherentColimitUnitRightTailValueTo B (a := a) (b := b)) _ _ ≪≫ _ = _
  rw [hs]
  simpa only [Iso.trans_assoc] using hc

end SerrePositivity.InfinityCategories.F2
