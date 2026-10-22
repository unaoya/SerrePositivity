module

public import SerrePositivity.InfinityCategories.F1B.KanEquivalenceLiftingInvertible

/-!
概要：終点指定の可逆辺の持ち上げにより、元の像と同型な頂点を厳密に回収する。
方針：元の頂点同型の射を一辺で表し、同じ終点と同じ辺を持ち上げて始点を取る。
規約：結論は指定した元の頂点への射影の等式。
使われ方：新しい辺と元の双普遍四角形の下辺の全自然同型から厳密な下辺を得る。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の像の頂点と同型な指定頂点は、終点指定持ち上げにより元の全体の頂点へ厳密に戻る。 -/
lemma exists_strict_vertex_preimage_of_targetLifting {E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (hp : F1B.KanInvertibleTargetLifting p) (x : E _⦋0⦌) (y : B _⦋0⦌)
    (e : VertexIso y (p.app (Opposite.op ⦋0⦌) x)) :
    ∃ z : E _⦋0⦌, p.app (Opposite.op ⦋0⦌) z = y := by
  obtain ⟨k, hk⟩ := homotopyCategory_homMk_surjective y (p.app (Opposite.op ⦋0⦌) x) e.hom
  have hi : IsInvertibleEdge k := by
    change IsIso (SSet.Truncated.HomotopyCategory.homMk k)
    rw [hk]
    infer_instance
  have ht : stdSimplex.δ (0 : Fin 2) ≫ SSet.yonedaEquiv.symm k.edge =
      SSet.yonedaEquiv.symm (p.app (Opposite.op ⦋0⦌) x) := by
    rw [stdSimplex.δ_comp_yonedaEquiv_symm]
    exact congrArg SSet.yonedaEquiv.symm k.tgt_eq
  obtain ⟨l, _hlt, hlp, _hli⟩ := hp x (SSet.yonedaEquiv.symm k.edge)
    (by
      exact (isInvertibleEdge_congr (e := k) (f := edgeOfSimplex
        (SSet.yonedaEquiv (SSet.yonedaEquiv.symm k.edge)))
        (SSet.yonedaEquiv.apply_symm_apply k.edge).symm).mp hi) ht
  refine ⟨SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) ≫ l), ?_⟩
  have h : (stdSimplex.δ (1 : Fin 2) ≫ l) ≫ p = SSet.yonedaEquiv.symm y := by
    rw [Category.assoc, hlp, stdSimplex.δ_comp_yonedaEquiv_symm]
    exact congrArg SSet.yonedaEquiv.symm k.src_eq
  have hh := congrArg SSet.yonedaEquiv h
  simpa only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using hh

end SerrePositivity.InfinityCategories.F2.Idempotent
