module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitRawFirstChoiceSpecifiedComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitRawFirstConstantVertexData
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativeFunctorCurryIsoPresentation
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerAlgebra

/-!
概要：全第一辺終点比較の後合成も、元の指定一点比較の後合成へ値まで戻す。
方針：実二頂点の評価式を使い、同じ内部 Hom の作用で指定比較を写す。
規約：元の実二頂点と指定比較を保持。使われ方：全長辺比較の自然性の元の値への反映。
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
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (a : SSet.Homotopy F G)
local notation "P" => coherentColimitRawConstantFiberProjection B F
local notation "K" => leftUnstraightening (coherentColimitRawConstantDiagram B F)
local notation "x" => coherentColimitRawFirstChoiceConstantVertex B a
local notation "y" => coherentColimitRawFirstChoiceUniversalVertex B a P
local notation "n" => IsContractibleKan.vertexIso
  (coherentColimitRawFirstChoiceSpace_isContractibleKan B a P) x y

/-- 元の実第一辺比較を任意の実射で写しても、元の同じ指定一点比較の後合成になる。 -/
lemma coherentColimitRawFirstChoiceEndpoint_specified_post_heq {X : SSet.{u + 1}}
    (t : vertexFiber pointedSpaceProjection
      (JoinCocone.vertex (coherentDiagramTotalCocone G)) ⟶ X) :
    HEq (VertexIso.map
      (VertexIso.map n (curry (coherentColimitRawFirstChoiceEndpoint B a P)))
      ((ihom K).map t)) ((coherentColimitConstantTransportRawPointIso B a).postcomp t) := by
  have hm := vertexIso_map_heq_of_heq _ _
    (coherentColimitRawFirstChoiceEndpoint_constant_vertex B a)
    (coherentColimitRawFirstChoiceEndpoint_universal_vertex B a)
    (coherentColimitRawFirstChoiceEndpoint_specified_heq B a) ((ihom K).map t)
  simpa only [coherentColimitRawConstantDiagram, VertexIso.map, functorIso_postcomp_eq_mapIso,
    hoFunctor_map,
    Functor.toCatHom_toFunctor] using hm

end SerrePositivity.InfinityCategories.F2
