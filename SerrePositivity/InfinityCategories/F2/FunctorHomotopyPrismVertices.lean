module

public import SerrePositivity.InfinityCategories.F2.FunctorHomotopyPrismEvaluation
public import SerrePositivity.InfinityCategories.F2.FunctorHomotopySourceComparison
public import SerrePositivity.InfinityCategories.F2.RelativeRestrictedEndpointVertex

/-!
概要：始点も動く全 prism 空間の評価と切断の各点を、元の実証拠へ厳密に戻す。
方針：全相対端点評価の頂点公式と元の普遍 prism の定義を使う。
規約：元の prism・始点・終点を保持。使われ方：全自然な比較と F1 指定比較の照合。
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
local notation "x" => relativeFunctorVertex pointedSpaceProjection d
  (RelativeExtensionEndpointWitness.extension w) (RelativeExtensionEndpointWitness.over w)

/-- 全 prism 空間の始点評価は、元の同じ実始域射の頂点を返す。 -/
lemma functorHomotopyPrismSourceEvaluation_vertex :
    (functorHomotopyPrismSourceEvaluation H p).app _ x =
      relativeFunctorVertex (leftUnstraighteningProjection F) p s hi :=
  relativeFunctorRestrictedEndpoint_vertex pointedSpaceProjection d (prismEndpoint 0 C)
    F p (functorHomotopyPrismBase_source H p) w.extension w.over s hi w.initial

/-- 全 prism 空間の終点評価は、元の同じ実終点射の頂点を返す。 -/
lemma functorHomotopyPrismTargetEvaluation_vertex :
    (functorHomotopyPrismTargetEvaluation H p).app _ x =
      relativeFunctorVertex (leftUnstraighteningProjection G) p w.endpoint w.endpoint_over :=
  relativeFunctorRestrictedEndpoint_vertex pointedSpaceProjection d (prismEndpoint 1 C)
    G p (functorHomotopyPrismBase_target H p) w.extension w.over w.endpoint w.endpoint_over
    w.evaluate

/-- 全始域射の普遍切断の元の一点は、同じ普遍 prism の元の証拠そのもの。 -/
lemma functorHomotopyPrismSection_vertex :
    (functorHomotopyPrismSection H p).app _
      (relativeFunctorVertex (leftUnstraighteningProjection F) p s hi) =
      relativeFunctorVertex pointedSpaceProjection d
        (functorHomotopySourceCanonicalWitness H p s hi).extension
        (functorHomotopySourceCanonicalWitness H p s hi).over := by
  apply Subtype.ext
  rfl

end SerrePositivity.InfinityCategories.F2
