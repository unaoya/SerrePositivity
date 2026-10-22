module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitRightTailUnitCancellation
public import SerrePositivity.InfinityCategories.F2.VertexIsoMiddleEndpointExchange

/-!
概要：a6 の元の模型三角形式から、下側輸送因子と最後辺の上側単位因子を消去する。
方針：同じ実中間頂点の表示を前置比較へ移し、元の残り二因子の単位消去を代入する。
規約：元の三角形と三辺の模型比較を保持。使われ方：同じ全区間族の比較の反映。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u}) [Quasicategory B]
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d)
local notation "u₀" => Subtype.val (leftUnstraighteningMappingVertexMap F
  (SSet.const (JoinCocone.vertex (coherentDiagramTotalCocone F)))
  (coconeTransformationVertex (coherentDiagramTotalCocone F)))
local notation "V" => pointedFiberValueTo (coherentDiagramTotalCocone_vertex J)
local notation "f" => Subtype.val (leftUnstraighteningMappingVertexMap F G
  (coherentVertexOfHomotopy a))
local notation "R" => vertexIsoOfEq
  (Iso.symm (FunctorIso.postcomp
    (FunctorIso.precomp (coherentColimitConstantTriangleRemainderIso B T) u₀) V))
  (coherentColimitLowerPoint_target_valueTo_vertex B d) rfl

omit [Quasicategory B] in
/-- 元の長辺輸送の残りを、同じ元の最初因子の実始点へ表示変更した指定比較。 -/
def coherentColimitIntervalModelTransportRemainder :=
  vertexIsoOfEq R rfl
    ((coherentColimitConstantTriangleValueTo_target_vertex B (a := a) (b := b)).symm.trans
      (coherentColimitFirstPost_valueTo_source_vertex B a b))

/-- 元の模型三角形式では、両外側因子が同じ輸送の残りと最後辺の模型比較へ消去される。 -/
lemma coherentColimitIntervalModel_outer_cancel :
    coherentColimitIntervalModelUnitComparison B d ≪≫
      vertexIsoOfEq (coherentTotalTriangleNativeModelComparison T)
        (congrArg functorVertex (coherentColimitNativeModelTarget_eq_unit B d))
        (congrArg functorVertex (coherentTotalTriangleNativeModelTarget_eq_unit a b)) =
    coherentColimitIntervalModelTransportRemainder B T ≪≫
      coherentColimitRightTailTransportValueTo B a b ≪≫
        (coherentColimitIntervalModelUnitComparison B b).precomp f := by
  have hm := vertexIsoOfEq_change_middle R
    (coherentColimitUnitRightTailValueTo B (a := a) (b := b))
    (coherentColimitConstantTriangleValueTo_target_vertex B (a := a) (b := b))
    (coherentColimitFirstPost_valueTo_source_vertex B a b)
    (coherentColimitValueProjection_composite_vertex B a b)
  have ht := congrArg (fun k => k ≪≫ (coherentColimitUpperUnitFactorIso B b).precomp f) hm
  have h := (coherentColimitIntervalModel_lower_cancel B T).trans
    (by simpa only [Iso.trans_assoc] using ht)
  simpa only [Iso.trans_assoc, coherentColimitRightTail_valueTo_unit_cancel,
    coherentColimitIntervalModelTransportRemainder] using h

end SerrePositivity.InfinityCategories.F2
