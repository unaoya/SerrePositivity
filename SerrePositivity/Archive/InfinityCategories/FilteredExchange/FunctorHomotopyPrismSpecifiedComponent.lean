module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorHomotopyExtensionEndpoint
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoComponentPost
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorHomotopySourceComponent

/-!
概要：始点も動く全 prism 比較の各点成分を、元の初期値固定の指定比較へ値まで同定する。
方針：始点射影の像が同じ恒等同型となることを、充満忠実性で反映する。
規約：元の実証拠・同型を保持。使われ方：F1 の指定始域比較へ全自然性を移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B C : SSet.{u + 1}} {F G : B ⟶ SpaceInfinity.{u}}
  (H : SSet.Homotopy F G) (p : C ⟶ B) (s : C ⟶ leftUnstraightening F)
  (hi : s ≫ leftUnstraighteningProjection F = p)
  (w : RelativeExtensionEndpointWitness pointedSpaceProjection
    ((Δ[1] ◁ p) ≫ functorSimplexDiagram (curry H.h)) (prismEndpoint 0 C)
    (s ≫ pullback.fst pointedSpaceProjection F) (prismEndpoint 1 C) G p)
local notation "d" => (Δ[1] ◁ p) ≫ functorSimplexDiagram (curry H.h)
local notation "v" => s ≫ pullback.fst pointedSpaceProjection F
local notation "hv" => RelativeExtensionEndpointWitness.initial_base w
local notation "r" =>
  relativeFunctorExtensionSpaceι pointedSpaceProjection d (prismEndpoint 0 C) v hv
local notation "q" => functorHomotopyPrismSourceEvaluation H p
local notation "z" => functorHomotopySourceCanonicalWitness H p s hi
local notation "x" => relativeFunctorVertex pointedSpaceProjection d
  (RelativeExtensionEndpointWitness.extension w) (RelativeExtensionEndpointWitness.over w)
local notation "hc" => relativeFunctorExtensionSpace_isContractibleKan pointedSpaceProjection d
  (prismEndpoint 0 C) (prismEndpoint_zero_leftAnodyne C) v hv

/-- 始点も動く全自然な終点比較は、元の証拠で F1 の同じ指定始域比較を回収する。 -/
lemma functorHomotopyPrismEndpointComparison_heq_specified :
    HEq ((functorHomotopyPrismEndpointComparison H p).app x)
      (functorHomotopySourceEndpointIso H p s hi w) := by
  let e := functorHomotopyPrismSectionComparison H p
  let R := functorHomotopyPrismTargetEvaluation H p
  have hs := congrArg (fun k => q ≫ k) (functorHomotopyPrismSection_target H p)
  have hs' := (Category.assoc q (functorHomotopyPrismSection H p) R).trans hs
  have hη : HEq (functorHomotopyPrismEndpointComparison H p) (e.postcomp R) := by
    change HEq ((functorEqIso hs').symm ≪≫ e.postcomp R ≪≫
      functorEqIso (Category.id_comp R)) (e.postcomp R)
    simp only [functorEqIso_eqToIso]
    exact iso_endpoints_heq (e.postcomp R)
      (congrArg (fun k => SSet.HomotopyCategory.mk (functorVertex k)) hs')
      (congrArg (fun k => SSet.HomotopyCategory.mk (functorVertex k)) (Category.id_comp R))
  have he := functorIso_app_heq_of_heq (functorHomotopyPrismEndpointComparison H p)
    (e.postcomp R) hs'.symm (Category.id_comp R).symm hη x
  have ha : (q ≫ functorHomotopyPrismSection H p).app _ x =
      (r).app _ ((z).point hv) := by
    change (functorHomotopyPrismSection H p).app _ ((q).app _ x) = _
    rw [functorHomotopyPrismSourceEvaluation_vertex H p s hi w,
      functorHomotopyPrismSection_vertex H p s hi]
    rfl
  have hm := vertexIso_map_heq_of_heq (e.app x)
    (functorHomotopyExtensionComparison H p s hi w) ha rfl
    (functorHomotopyPrismSectionComparison_heq_extension H p s hi w) R
  exact he.trans ((functorIso_app_postcomp_heq e R x).trans
    (hm.trans (functorHomotopySourceEndpointIso_heq_extension H p s hi w).symm))

/-- 全自然な比較は、元の実 prism を保持する F1 全族比較の同じ指定成分を返す。 -/
lemma functorHomotopyPrismEndpointComparison_heq_F1_component :
    HEq ((functorHomotopyPrismEndpointComparison H p).app x)
      (VertexIso.map
        ((functorHomotopySourceFamilyComparison H p s hi w).app
          (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))
        (relativeFunctorPre (leftUnstraighteningProjection G) p (𝟙 C))) :=
  (functorHomotopyPrismEndpointComparison_heq_specified H p s hi w).trans
    (functorHomotopySourceEndpointIso_heq_component H p s hi w)

end SerrePositivity.InfinityCategories.F2
