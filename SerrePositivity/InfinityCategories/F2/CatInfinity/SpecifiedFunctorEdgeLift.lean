module

public import SerrePositivity.InfinityCategories.F1B.Fibrations.EquivalenceLiftingInvertible

/-!
概要：指定された可逆な関手の辺を前合成に沿って持ち上げる。
方針：既存の相対 Kan の終点指定の充填を使う。
規約：新しい関手の制限と辺の像は厳密に一致する。
使われ方：Cat_∞ の錐の相対的な輸送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：関手の制限の指定可逆辺を終点を保って厳密に持ち上げる。
方針：単射による前合成の可逆辺持ち上げ性を適用し、両端を実際の関手に戻す。
規約：元の辺の像をホモトピー類だけでなく厳密に保持する。
使われ方：錐の頂点と図式の指定自然変換を同時に追跡する。 -/
lemma exists_precomposition_edge_lift {A B X : SSet.{u}} [Quasicategory X]
    (i : A ⟶ B) [Mono i] (f : A ⟶ X) (g : B ⟶ X)
    (e : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom A).obj X))
      (functorVertex f) (functorVertex (i ≫ g))) (he : IsInvertibleEdge e) :
    ∃ w : B ⟶ X, i ≫ w = f ∧
      ∃ l : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom B).obj X))
        (functorVertex w) (functorVertex g),
        ((pre i).app X).app (Opposite.op ⦋1⦌) l.edge = e.edge ∧ IsInvertibleEdge l := by
  let p := (pre i).app X
  have hp : SerrePositivity.InfinityCategories.F1B.EquivalenceLifting p := SerrePositivity.InfinityCategories.F1B.equivalenceLifting_pre (X := X) i
  let a : ((ihom A).obj X) _⦋1⦌ := e.edge
  have ha : SSet.yonedaEquiv (SSet.yonedaEquiv.symm a) = a :=
    SSet.yonedaEquiv.apply_symm_apply a
  have hi : IsInvertibleEdge (edgeOfSimplex (SSet.yonedaEquiv (SSet.yonedaEquiv.symm a))) :=
    (isInvertibleEdge_congr (e := e)
      (f := edgeOfSimplex (SSet.yonedaEquiv (SSet.yonedaEquiv.symm a))) ha.symm).mp he
  obtain ⟨L, hLt, hLp, hLi⟩ := hp.invertibleTargetLifting (functorVertex g)
    (SSet.yonedaEquiv.symm a) hi
    (by
      rw [stdSimplex.δ_comp_yonedaEquiv_symm]
      exact congrArg SSet.yonedaEquiv.symm e.tgt_eq)
  let z := ((ihom B).obj X).δ 1 (SSet.yonedaEquiv L)
  let w := (functorVertexEquiv B X).symm z
  have hw : functorVertex w = z := (functorVertexEquiv B X).apply_symm_apply z
  have ht : ((ihom B).obj X).δ 0 (SSet.yonedaEquiv L) = functorVertex g := by
    have h := congrArg SSet.yonedaEquiv hLt
    rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply] at h
    exact h
  have hm : p.app (Opposite.op ⦋0⦌) z = functorVertex f := by
    have h := congrArg (fun t ↦ stdSimplex.δ (1 : Fin 2) ≫ t) hLp
    rw [← Category.assoc, stdSimplex.δ_comp_yonedaEquiv_symm] at h
    have h' := congrArg SSet.yonedaEquiv h
    rw [SSet.yonedaEquiv_comp, stdSimplex.yonedaEquiv_δ_comp,
      Equiv.apply_symm_apply] at h'
    exact h'.trans e.src_eq
  have hmap : p.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv L) = e.edge := by
    rw [← SSet.yonedaEquiv_comp, hLp, Equiv.apply_symm_apply]
  refine ⟨w, ?_, ⟨SSet.yonedaEquiv L, hw.symm, ht⟩, hmap, ?_⟩
  · apply functorVertex_injective
    change p.app (Opposite.op ⦋0⦌) (functorVertex w) = functorVertex f
    rw [hw]
    exact hm
  · exact (isInvertibleEdge_congr (e := edgeOfSimplex (SSet.yonedaEquiv L))
      (f := (⟨SSet.yonedaEquiv L, hw.symm, ht⟩ : SSet.Truncated.Edge
        (X := (truncation 2).obj ((ihom B).obj X)) (functorVertex w) (functorVertex g)))
      rfl).mp hLi

end SerrePositivity.InfinityCategories.F2
