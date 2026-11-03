module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitRawLastLongValueEndpoints

/-!
概要：元の模型三角形式の長辺残余と指定一点比較を、同じ新長辺残余へ厳密に消去する。
方針：実三頂点で元の単位と値への像を揃え、同じ三比較の指定消去式を反映する。
規約：元の模型三角形と指定値を保持。使われ方：元の a6 比較式の残る三因子への縮約。
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
local notation "R₀" => Iso.symm (FunctorIso.postcomp
  (FunctorIso.precomp (coherentColimitConstantTriangleRemainderIso B T) u₀) V)
local notation "E" => FunctorIso.postcomp
  (FunctorIso.precomp (coherentColimitRawLastPointActionIso B a b) u₀) V
local notation "R₁" => Iso.symm (FunctorIso.postcomp
  (FunctorIso.precomp (coherentColimitRawLastLongRemainderIso B T) u₀) V)
local notation "e" => FunctorIso.precomp (coherentColimitConstantPointValueToIso B b)
  (coherentColimitRawLowerCompositeAction B a)

/-- 同じ新長辺残余の逆の元の単位・値への像を、元の模型三角形式の実両端へ戻す。 -/
def coherentColimitIntervalModelRawLastRemainder :=
  vertexIsoOfEq R₁ (coherentColimitLowerPoint_target_valueTo_vertex B d)
    (coherentColimitRawLastLongValue_target_vertex B a b)

/-- 元の模型残余と元の最後辺の指定一点比較は、同じ新長辺残余へ厳密に消去される。 -/
lemma coherentColimitIntervalModel_raw_last_prefix_cancel :
    coherentColimitIntervalModelTransportRemainder B T ≪≫ e =
      coherentColimitIntervalModelRawLastRemainder B T := by
  have hr : HEq (coherentColimitIntervalModelTransportRemainder B T) R₀ := by
    exact (vertexIsoOfEq_heq _ _ _).trans (vertexIsoOfEq_heq _ _ _)
  have ht := vertexIso_trans_heq_of_heq
    (coherentColimitIntervalModelTransportRemainder B T) e R₀ E
    (coherentColimitLowerPoint_target_valueTo_vertex B d).symm
    (coherentColimitRawLastLongValue_middle_vertex B a b).symm
    (coherentColimitRawLastLongValue_target_vertex B a b).symm hr
    (coherentColimitRawLastPointAction_value_heq_point B a b).symm
  have hc := coherentColimitRawLastLong_inverse_middle_cancel_precomp_postcomp B T u₀ V
  exact eq_of_heq (ht.trans ((heq_of_eq hc).trans (vertexIsoOfEq_heq _ _ _).symm))

end SerrePositivity.InfinityCategories.F2
