module

public import SerrePositivity.InfinityCategories.F1B.KanEquivalenceLiftingInvertible

/-!
概要：isofibration の上の頂点の同型を終点指定で持ち上げる。
方針：同型の辺代表を持ち上げ、その始点と可逆な辺の類を取り出す。
規約：新しい始点の像は指定された頂点と厳密に等しい。
使われ方：図式固定の余錐の像を同型な指定余錐へ直す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：像の頂点への同型を、既知の終点の上の頂点同型へ持ち上げられる。
方針：同型の辺代表を終点指定で持ち上げ、両端と像の式を読む。
規約：像の同型の始点 y を厳密に実現する。
使われ方：底の余錐の同型に沿って相対余極限を移す。 -/
lemma exists_kanVertexIso_lift_target {V B : SSet.{u}} [Quasicategory B]
    (p : V ⟶ B) (hp : KanEquivalenceLifting p) (x : V _⦋0⦌) (y : B _⦋0⦌)
    (e : VertexIso y (p.app (Opposite.op ⦋0⦌) x)) :
    ∃ z : V _⦋0⦌, p.app (Opposite.op ⦋0⦌) z = y ∧ Nonempty (VertexIso z x) := by
  obtain ⟨a, ha⟩ := homotopyCategory_homMk_surjective _ _ e.hom
  have hai : IsInvertibleEdge a := by
    change IsIso (SSet.Truncated.HomotopyCategory.homMk a)
    rw [ha]
    infer_instance
  obtain ⟨L, hL₁, hLp, hi⟩ := hp.invertibleTargetLifting x (SSet.yonedaEquiv.symm a.edge)
    ((isInvertibleEdge_congr (e := a)
      (f := edgeOfSimplex (SSet.yonedaEquiv (SSet.yonedaEquiv.symm a.edge)))
      (SSet.yonedaEquiv.apply_symm_apply a.edge).symm).1 hai)
    (by
      rw [stdSimplex.δ_comp_yonedaEquiv_symm]
      exact congrArg SSet.yonedaEquiv.symm (show B.δ 0 a.edge = _ from a.tgt_eq))
  let z := V.δ 1 (SSet.yonedaEquiv L)
  have ht : V.δ 0 (SSet.yonedaEquiv L) = x := by
    have h := congrArg SSet.yonedaEquiv hL₁
    rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply] at h
    exact h
  have hm : p.app (Opposite.op ⦋0⦌) z = y := by
    have h := congrArg (fun t ↦ stdSimplex.δ (1 : Fin 2) ≫ t) hLp
    rw [← Category.assoc, stdSimplex.δ_comp_yonedaEquiv_symm] at h
    have h' := congrArg SSet.yonedaEquiv h
    rw [SSet.yonedaEquiv_comp, stdSimplex.yonedaEquiv_δ_comp,
      Equiv.apply_symm_apply] at h'
    exact h'.trans (show B.δ 1 a.edge = y from a.src_eq)
  have ei : VertexIso z (V.δ 0 (SSet.yonedaEquiv L)) :=
    asIso (SSet.Truncated.HomotopyCategory.homMk (edgeOfSimplex (SSet.yonedaEquiv L)))
  exact ⟨z, hm, ⟨ei ≪≫ eqToIso (congrArg (fun v ↦ HomotopyCategory.mk v) ht)⟩⟩

end SerrePositivity.InfinityCategories.F1B
