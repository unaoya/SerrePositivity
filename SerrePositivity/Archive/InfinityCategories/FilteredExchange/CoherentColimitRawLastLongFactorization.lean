module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitRawFirstChoiceSpecifiedPost
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitRawFirstChoicePostVertices
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitRawFirstChoiceUniversalComponent
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitRawFirstChoiceConstantComponent
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.VertexIsoCompositionTransport

/-!
概要：元の新長辺残余を、元の第一辺指定比較と同じ普遍三角形比較へ分解する。
方針：全第一辺選択上の自然性を元の二実頂点で評価し、三つの指定値を回収する。
規約：元の全二単体・実頂点・指定比較を保持。使われ方：元の模型三角形式の残余の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d)
local notation "P" => coherentColimitRawConstantFiberProjection B F
local notation "K" => leftUnstraightening (coherentColimitRawConstantDiagram B F)
local notation "x" => coherentColimitRawFirstChoiceConstantVertex B a
local notation "y" => coherentColimitRawFirstChoiceUniversalVertex B a P
local notation "n" => IsContractibleKan.vertexIso
  (coherentColimitRawFirstChoiceSpace_isContractibleKan B a P) x y
local notation "t" => coherentColimitRawFiberTransport B b

/-- 元の新長辺残余は、同じ第一辺指定比較の最後辺輸送と普遍二辺比較の合成。 -/
lemma coherentColimitRawLastLongRemainderIso_heq_factorization :
    HEq (((coherentColimitConstantTransportRawPointIso B a).postcomp t) ≪≫
      coherentColimitRawUniversalTriangleComparison B T P)
      (coherentColimitRawLastLongRemainderIso B T) := by
  have h := coherentColimitRawFirstChoiceTriangleComparison_first_transport B T P n
  have hp := vertexIso_trans_heq_of_heq _ _
    ((coherentColimitConstantTransportRawPointIso B a).postcomp t)
    (coherentColimitRawUniversalTriangleComparison B T P)
    (coherentColimitRawFirstChoiceEndpoint_post_constant_vertex B a t)
    (coherentColimitRawFirstChoiceEndpoint_post_universal_vertex B a t) rfl
    (coherentColimitRawFirstChoiceEndpoint_specified_post_heq B a t)
    (coherentColimitRawFirstChoiceTriangleComparisonApp_universal_heq B T P)
  exact hp.symm.trans ((heq_of_eq h).trans
    (coherentColimitRawFirstChoiceTriangleComparisonApp_constant_heq B T))

/-- 元の新長辺残余を、同じ元の raw 普遍長辺終点へ正規化した指定同型。 -/
def coherentColimitRawLastLongNormalizedRemainderIso :=
  functorIsoOfEq (coherentColimitRawLastLongRemainderIso B T) rfl
    (coherentColimitConstantTransport_raw_point_target B d)

/-- 元の実両端へ正規化すると、同じ新長辺残余の分解は同じ型の厳密な等式。 -/
lemma coherentColimitRawLastLongNormalizedRemainderIso_eq_factorization :
    coherentColimitRawLastLongNormalizedRemainderIso B T =
      ((coherentColimitConstantTransportRawPointIso B a).postcomp t) ≪≫
        coherentColimitRawUniversalTriangleComparison B T P := by
  exact eq_of_heq ((functorIsoOfEq_heq _ _ _).trans
    (coherentColimitRawLastLongRemainderIso_heq_factorization B T).symm)

end SerrePositivity.InfinityCategories.F2
