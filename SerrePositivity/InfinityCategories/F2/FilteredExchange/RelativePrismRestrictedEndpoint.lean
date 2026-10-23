module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativePrismEndpointComparisons
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativePrismEndpointPrecomposition
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceSimplexPointedRestrictionNaturality

/-!
概要：元の全図式の相対同型を辺で制限した実終点像は、同じ元の全終点評価の像。
方針：同じ指定同型の二段の像と、相対前合成の合成式を厳密に合わせる。
規約：指定値を保持。使われ方：全三角形の最後面と終頂点比較の同じ値の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {D E B A : SSet.{u}} (p : E ⟶ B) (β : D ⟶ B)
  (r : (Δ[1] : SSet.{u}) ⊗ A ⟶ D)
  (W W' : D ⟶ E) (hW : W ≫ p = β) (hW' : W' ≫ p = β)
  (z : B _⦋0⦌) (h : (prismEndpoint 1 A ≫ r) ≫ β = SSet.const z)
  (g g' : A ⟶ vertexFiber p z)
  (he : prismEndpoint 1 A ≫ (r ≫ W) = g ≫ vertexFiberι p z)
  (he' : prismEndpoint 1 A ≫ (r ≫ W') = g' ≫ vertexFiberι p z)
  (e : VertexIso (relativeFunctorVertex p β W hW) (relativeFunctorVertex p β W' hW'))
local notation "hR" => Eq.trans (Eq.symm (Category.assoc (prismEndpoint 1 A) r β)) h
local notation "eR" => vertexIsoOfEq (VertexIso.map e (relativeFunctorPre p β r))
  (relativeFunctorPre_vertex p β r W hW) (relativeFunctorPre_vertex p β r W' hW')

/-- 元の全相対比較の辺制限の実終点像は、同じ全図式での終点像と値まで一致する。 -/
lemma relativePrismActualEndpointIso_restrict_heq :
    HEq (relativePrismActualEndpointIso p (r ≫ β) z hR (r ≫ W) (r ≫ W')
      (by rw [Category.assoc, hW]) (by rw [Category.assoc, hW']) g g' he he' eR)
      (VertexIso.map e (relativeFunctorPre p β (prismEndpoint 1 A ≫ r) ≫
        eqToHom (congrArg (relativeFunctorSpace p) h) ≫ relativeFunctorConstFiberHom p z)) := by
  unfold relativePrismActualEndpointIso
  refine (vertexIsoOfEq_heq _ _ _).trans ?_
  have hs := vertexIsoOfEq_map_heq (VertexIso.map e (relativeFunctorPre p β r))
    (relativeFunctorPre_vertex p β r W hW) (relativeFunctorPre_vertex p β r W' hW')
    (curry (relativePrismEvaluationEndpoint p (r ≫ β) 1 z hR))
  rw [vertexIso_map_comp] at hs
  exact hs.trans (vertexIso_map_heq e
    (relativePrismEvaluationEndpoint_restrict_eq_pre p β r 1 z h))

end SerrePositivity.InfinityCategories.F2
