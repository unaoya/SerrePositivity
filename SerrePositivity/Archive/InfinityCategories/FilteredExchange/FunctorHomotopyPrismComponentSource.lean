module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorHomotopyPrismComparison
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoComponentPost
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorHomotopyPrismVertices
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.VertexIsoFaithfulHEq

/-!
概要：始点も動く全 prism の普遍持ち上げと元の実 prism を、始点上で比較する。
方針：始点評価の厳密な切断と全境界持ち上げから、同じ fiber 内の全関手同型を取る。
規約：元の切断と実終点を保持。使われ方：共有辺の指定比較の全自然性。
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
  (H : SSet.Homotopy F G) (p : C ⟶ B)
local notation "d" => (Δ[1] ◁ p) ≫ functorSimplexDiagram (curry H.h)
local notation "L" => relativeFunctorSpace pointedSpaceProjection d
local notation "q" => functorHomotopyPrismSourceEvaluation H p
local notation "r" => functorHomotopyPrismTargetEvaluation H p
local notation "s" => functorHomotopyPrismSection H p

/-- 全 prism 比較の各点成分は、始点射影で元の同じ始点の等式の同型へ戻る。 -/
lemma functorHomotopyPrismSectionComparison_app_source (x : L _⦋0⦌) :
    HEq (VertexIso.map ((functorHomotopyPrismSectionComparison H p).app x) q)
      (eqToIso (congrArg SSet.HomotopyCategory.mk
        (congrArg (fun k : L ⟶ _ => k.app (Opposite.op ⦋0⦌) x)
          (functorHomotopyPrismSectionComparison_over H p)))) := by
  have h₀ := functorIso_app_postcomp_heq (functorHomotopyPrismSectionComparison H p) q x
  have h₁ := congrArg (fun e => FunctorIso.app e x)
    (functorHomotopyPrismSectionComparison_source H p)
  exact h₀.symm.trans ((heq_of_eq h₁).trans
    (functorIso_app_eqToIso_heq (functorHomotopyPrismSectionComparison_over H p) x))

/-- 元の実証拠で読むと、全比較の始点像は同じ元の指定始域射の恒等同型となる。 -/
lemma functorHomotopyPrismSectionComparison_witness_source
    (i : C ⟶ leftUnstraightening F) (hi : i ≫ leftUnstraighteningProjection F = p)
    (w : RelativeExtensionEndpointWitness pointedSpaceProjection d (prismEndpoint 0 C)
      (i ≫ pullback.fst pointedSpaceProjection F) (prismEndpoint 1 C) G p) :
    HEq (VertexIso.map ((functorHomotopyPrismSectionComparison H p).app
      (relativeFunctorVertex pointedSpaceProjection d w.extension w.over)) q)
      (Iso.refl (SSet.HomotopyCategory.mk
        (relativeFunctorVertex (leftUnstraighteningProjection F) p i hi))) := by
  let x := relativeFunctorVertex pointedSpaceProjection d w.extension w.over
  have hc := functorHomotopyPrismSectionComparison_app_source H p x
  have hx := functorHomotopyPrismSourceEvaluation_vertex H p i hi w
  have hr {a b c : hoFunctor.obj (relativeFunctorSpace (leftUnstraighteningProjection F) p)}
      (h : a = b) (hb : b = c) : HEq (eqToIso h) (Iso.refl c) := by
    cases h
    cases hb
    rfl
  exact hc.trans (hr _ (congrArg SSet.HomotopyCategory.mk hx))

end SerrePositivity.InfinityCategories.F2
