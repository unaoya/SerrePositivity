module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativePrismInitialEndpoint
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativePrismEndpointPrecomposition

/-!
概要：辺制限後の指定相対比較の両端像を、元の全図式の同じ端点評価へ戻す。
方針：二段の相対前合成と全端点評価の厳密な射の等式を使う。
規約：両端の指定値を保持。使われ方：最後面の中間・終点比較の同時照合。
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
  (e : VertexIso (relativeFunctorVertex p β W hW) (relativeFunctorVertex p β W' hW'))
local notation "eR" => vertexIsoOfEq (VertexIso.map e (relativeFunctorPre p β r))
  (relativeFunctorPre_vertex p β r W hW) (relativeFunctorPre_vertex p β r W' hW')

/-- 同じ辺の両端で、制限後の指定像は元の全図式の同じ全端点評価の指定像。 -/
lemma relativePrismEndpointImage_restrict_heq (i : Fin 2) (z : B _⦋0⦌)
    (h : (prismEndpoint i A ≫ r) ≫ β = SSet.const z) :
    HEq (VertexIso.map eR (curry (relativePrismEvaluationEndpoint p (r ≫ β) i z
      ((Category.assoc (prismEndpoint i A) r β).symm.trans h))))
      (VertexIso.map e (relativeFunctorPre p β (prismEndpoint i A ≫ r) ≫
        eqToHom (congrArg (relativeFunctorSpace p) h) ≫ relativeFunctorConstFiberHom p z)) := by
  have hs := vertexIsoOfEq_map_heq (VertexIso.map e (relativeFunctorPre p β r))
    (relativeFunctorPre_vertex p β r W hW) (relativeFunctorPre_vertex p β r W' hW')
    (curry (relativePrismEvaluationEndpoint p (r ≫ β) i z
      ((Category.assoc (prismEndpoint i A) r β).symm.trans h)))
  rw [vertexIso_map_comp] at hs
  exact hs.trans (vertexIso_map_heq e
    (relativePrismEvaluationEndpoint_restrict_eq_pre p β r i z h))

/-- 同じ辺制限の実始点像も、元の全図式の同じ始点評価の指定値を保持する。 -/
lemma relativePrismInitialEndpointIso_restrict_heq (z : B _⦋0⦌)
    (h : (prismEndpoint 0 A ≫ r) ≫ β = SSet.const z)
    (g g' : A ⟶ vertexFiber p z)
    (he : prismEndpoint 0 A ≫ (r ≫ W) = g ≫ vertexFiberι p z)
    (he' : prismEndpoint 0 A ≫ (r ≫ W') = g' ≫ vertexFiberι p z) :
    HEq (relativePrismInitialEndpointIso p (r ≫ β) z
      ((Category.assoc (prismEndpoint 0 A) r β).symm.trans h) (r ≫ W) (r ≫ W')
      (by rw [Category.assoc, hW]) (by rw [Category.assoc, hW']) g g' he he' eR)
      (VertexIso.map e (relativeFunctorPre p β (prismEndpoint 0 A ≫ r) ≫
        eqToHom (congrArg (relativeFunctorSpace p) h) ≫ relativeFunctorConstFiberHom p z)) := by
  unfold relativePrismInitialEndpointIso
  exact (vertexIsoOfEq_heq _ _ _).trans
    (relativePrismEndpointImage_restrict_heq p β r W W' hW hW' e 0 z h)

end SerrePositivity.InfinityCategories.F2
