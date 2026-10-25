module

public import SerrePositivity.InfinityCategories.Core.SmallHullFactorization
public import SerrePositivity.InfinityCategories.Core.EquivalencePathInternalHom

/-!
概要：同じ小模型への関手族因子化と、指定可逆 path 族の回収。
方針：評価図式を因子化して curry し、指定点での同じ辺の可逆性を検査する。
規約：元の関手族・path 族と包含の厳密等号を保つ。
使われ方：Ind-S (4) の全前合成の境界資料。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 小さい次数を持つ形状でパラメーター化された関手族を同じ小模型へ因子化する。 -/
lemma SmallSubcomplex.Hull.factor_functor
    {E K T : SSet.{max u v}} {A : E.Subcomplex} (H : SmallSubcomplex.Hull.{u, v} E A)
    [∀ d, Small.{u} (K.obj d)] [∀ d, Small.{u} (T.obj d)]
    (a : T ⟶ (ihom K).obj E) (ha : SSet.Subcomplex.range (uncurry a) ≤ A) :
    ∃ b : T ⟶ (ihom K).obj ((SSet.uliftFunctor.{v, u}).obj H.obj),
      b ≫ (ihom K).map H.inclusion = a := by
  have (d : SimplexCategoryᵒᵖ) : Small.{u} ((K ⊗ T).obj d) :=
    inferInstanceAs (Small.{u} (K.obj d × T.obj d))
  obtain ⟨b, hb⟩ := H.factor_small (uncurry a) ha
  refine ⟨curry b, ?_⟩
  apply uncurry_injective
  rw [uncurry_natural_right, uncurry_curry, hb]

/-- 指定可逆 path 族の各点での元の一単体。 -/
def functorPathPointEdge {E K T : SSet.{u}}
    (a : T ⟶ equivalencePath ((ihom K).obj E)) (t : T _⦋0⦌) (k : K _⦋0⦌) : E _⦋1⦌ :=
  (evaluateFunctorAt (Y := E) k).app (Opposite.op ⦋1⦌)
    (intervalFunctorVertexEdge ((a ≫ equivalencePathι _).app (Opposite.op ⦋0⦌) t))

/-- 元の指定 path の各点の辺は可逆。 -/
lemma functorPathPointEdge_invertible {E K T : SSet.{u}}
    (a : T ⟶ equivalencePath ((ihom K).obj E)) (t : T _⦋0⦌) (k : K _⦋0⦌) :
    IsInvertibleEdge (edgeOfSimplex (functorPathPointEdge a t k)) := by
  have h := fullSubcomplexOnVertices_vertex (a.app (Opposite.op ⦋0⦌) t)
  change IsInvertibleEdge (edgeOfSimplex
    (intervalFunctorVertexEdge ((a ≫ equivalencePathι _).app (Opposite.op ⦋0⦌) t))) at h
  exact (isInvertibleEdge_congr (e := (edgeOfSimplex
    (intervalFunctorVertexEdge ((a ≫ equivalencePathι _).app (Opposite.op ⦋0⦌) t))).map
      ((truncation 2).map (evaluateFunctorAt (Y := E) k)))
    (f := edgeOfSimplex (functorPathPointEdge a t k)) rfl).mp (h.map (evaluateFunctorAt k))

/-- 同じ点辺の可逆性を保持した因子化は、元の可逆 path 族を厳密に持ち上げる。 -/
lemma exists_functorPath_lift {E Q K T : SSet.{u}} [Quasicategory Q]
    (j : Q ⟶ E) (a : T ⟶ equivalencePath ((ihom K).obj E))
    (b : T ⟶ (ihom (Δ[1] : SSet.{u})).obj ((ihom K).obj Q))
    (hb : b ≫ (ihom (Δ[1] : SSet.{u})).map ((ihom K).map j) = a ≫ equivalencePathι _)
    (hj : ∀ (t : T _⦋0⦌) (k : K _⦋0⦌) {x y : Q _⦋0⦌}
      (e : Truncated.Edge (X := (truncation 2).obj Q) x y),
      j.app (Opposite.op ⦋1⦌) e.edge = functorPathPointEdge a t k → IsInvertibleEdge e) :
    ∃ c : T ⟶ equivalencePath ((ihom K).obj Q),
      c ≫ equivalencePathMap ((ihom K).map j) = a := by
  have hv (t : T _⦋0⦌) : IsEquivalencePathVertex (b.app (Opposite.op ⦋0⦌) t) := by
    apply (isInvertibleEdge_iff_evaluateFunctorAt_any
      (edgeOfSimplex (intervalFunctorVertexEdge (b.app (Opposite.op ⦋0⦌) t)))).mpr
    intro k
    apply hj t k
    have hh := congrArg (fun f => f.app (Opposite.op ⦋0⦌) t) hb
    have hi := congrArg intervalFunctorVertexEdge hh
    change intervalFunctorVertexEdge
      (((ihom (Δ[1] : SSet.{u})).map ((ihom K).map j)).app (Opposite.op ⦋0⦌)
        (b.app (Opposite.op ⦋0⦌) t)) =
      intervalFunctorVertexEdge ((a ≫ equivalencePathι _).app (Opposite.op ⦋0⦌) t) at hi
    rw [intervalFunctorVertexEdge_map] at hi
    exact congrArg ((evaluateFunctorAt (Y := E) k).app (Opposite.op ⦋1⦌)) hi
  refine ⟨fullSubcomplexLift IsEquivalencePathVertex b hv, ?_⟩
  have : Mono (equivalencePathι ((ihom K).obj E)) := by
    unfold equivalencePathι
    infer_instance
  apply (cancel_mono (equivalencePathι ((ihom K).obj E))).1
  rw [Category.assoc, equivalencePathMap_ι, ← Category.assoc]
  have hc : fullSubcomplexLift IsEquivalencePathVertex b hv ≫ equivalencePathι ((ihom K).obj Q) = b :=
    fullSubcomplexLift_ι _ _ _
  rw [hc]
  exact hb

end SerrePositivity.InfinityCategories
