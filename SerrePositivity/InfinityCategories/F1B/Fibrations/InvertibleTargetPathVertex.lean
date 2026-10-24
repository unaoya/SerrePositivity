module

public import SerrePositivity.InfinityCategories.F1B.Fibrations.InvertibleTargetLiftingIso

/-!
概要：可逆辺の終点指定の持ち上げを可逆 path の頂点の持ち上げに直す。
方針：区間からの関手と内部 Hom の頂点の同値を往復する。
規約：像の path と終点を厳密に指定する。
使われ方：相対可逆 path の比較の零次元の境界充填。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：可逆辺を終点指定で持ち上げる射は可逆 path の頂点も持ち上げる。
方針：指定された path を区間からの射に戻し、辺の持ち上げを全部分複体へ戻す。
規約：圏の充填性を要求せず、指定した一次単体の像を保つ。
使われ方：相対 path 比較の全境界の充填の起点。 -/
lemma exists_kanEquivalencePathVertex_lift_of_targetLifting {E B : SSet.{u}}
    (p : E ⟶ B) (hp : SerrePositivity.InfinityCategories.F1B.InvertibleTargetLifting p) (x : E _⦋0⦌)
    (v : (equivalencePath B) _⦋0⦌)
    (hv : (equivalencePathEndpoint B 1).app (Opposite.op ⦋0⦌) v =
      p.app (Opposite.op ⦋0⦌) x) :
    ∃ w : (equivalencePath E) _⦋0⦌,
      (equivalencePathMap p).app (Opposite.op ⦋0⦌) w = v ∧
        (equivalencePathEndpoint E 1).app (Opposite.op ⦋0⦌) w = x := by
  obtain ⟨e, he⟩ := (functorVertexEquiv Δ[1] B).surjective v.val
  have hi := fullSubcomplexOnVertices_vertex v
  change IsEquivalencePathVertex v.val at hi
  rw [← he, functorVertexEquiv_apply, IsEquivalencePathVertex,
    intervalFunctorVertexEdge_functorVertex] at hi
  have hev : equivalencePathVertex (edgeOfSimplex (SSet.yonedaEquiv e)) hi = v := by
    apply Subtype.ext
    change functorVertex (SSet.yonedaEquiv.symm (SSet.yonedaEquiv e)) = v.val
    rw [Equiv.symm_apply_apply]
    exact he
  have ht : stdSimplex.δ (0 : Fin 2) ≫ e =
      SSet.yonedaEquiv.symm (p.app (Opposite.op ⦋0⦌) x) := by
    apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
    rw [← hev, equivalencePathVertex_one] at hv
    exact hv
  obtain ⟨l, hlt, hlp, hli⟩ := hp x e hi ht
  let w := equivalencePathVertex (edgeOfSimplex (SSet.yonedaEquiv l)) hli
  refine ⟨w, ?_, ?_⟩
  · apply Subtype.ext
    change functorVertex (SSet.yonedaEquiv.symm (SSet.yonedaEquiv l) ≫ p) = v.val
    rw [Equiv.symm_apply_apply, hlp]
    exact he
  · change (equivalencePathEndpoint E 1).app (Opposite.op ⦋0⦌)
      (equivalencePathVertex (edgeOfSimplex (SSet.yonedaEquiv l)) hli) = x
    rw [equivalencePathVertex_one]
    have h := congrArg SSet.yonedaEquiv hlt
    rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply] at h
    exact h

end SerrePositivity.InfinityCategories.F1B
