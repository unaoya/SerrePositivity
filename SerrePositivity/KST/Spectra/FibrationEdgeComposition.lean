module

public import SerrePositivity.KST.Spectra.FibrationCompositionTriangleLift
public import SerrePositivity.KST.Spectra.FundamentalLoopEdges

/-!
概要：二つ目の辺の射影が定数なら、合成辺の射影を一つ目の指定辺そのものに保って合成する。
方針：指定辺と恒等辺の退化三角形を二辺固定で持ち上げる。
規約：対角辺と三角形全体の射影を保持。使われ方：指定境界区間を保つ相対ホモトピー合成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra

/-- 退化三角形の持ち上げにより、合成後も射影を元の指定辺に厳密一致させる。 -/
lemma exists_edge_composite_over_path {E B : SSet.{u}} (p : E ⟶ B)
    (hp : SSet.modelCategoryQuillen.J.rlp p) {x y z : E _⦋0⦌} {u v : B _⦋0⦌}
    (f : E.Edge x y) (g : E.Edge y z) (r : B.Edge u v)
    (hf : SSet.yonedaEquiv.symm f.edge ≫ p = SSet.yonedaEquiv.symm r.edge)
    (hg : SSet.yonedaEquiv.symm g.edge ≫ p = SSet.const v) :
    ∃ e : E.Edge x z, ∃ t : SSet.Edge.CompStruct f g e,
      SSet.yonedaEquiv.symm e.edge ≫ p = SSet.yonedaEquiv.symm r.edge ∧
      SSet.yonedaEquiv.symm t.simplex ≫ p =
        SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.compId r).simplex := by
  let d := SSet.Edge.CompStruct.compId r
  have hid : SSet.yonedaEquiv.symm (SSet.Edge.id v).edge = SSet.const v := by
    have h := congrArg (fun e : B.Edge v v ↦ SSet.yonedaEquiv.symm e.edge)
      (FundamentalLoop.edge_const (X := B) (x := v))
    change SSet.yonedaEquiv.symm (SSet.yonedaEquiv (SSet.const v)) =
      SSet.yonedaEquiv.symm (SSet.Edge.id v).edge at h
    rw [Equiv.symm_apply_apply] at h
    exact h.symm
  have h₂ : SSet.yonedaEquiv.symm f.edge ≫ p =
      stdSimplex.δ (2 : Fin 3) ≫ SSet.yonedaEquiv.symm d.simplex := by
    rw [SSet.Edge.CompStruct.δ_two_yonedaEquiv_symm]
    exact hf
  have h₀ : SSet.yonedaEquiv.symm g.edge ≫ p =
      stdSimplex.δ (0 : Fin 3) ≫ SSet.yonedaEquiv.symm d.simplex := by
    rw [SSet.Edge.CompStruct.δ_zero_yonedaEquiv_symm, hid]
    exact hg
  obtain ⟨e, t, ht⟩ := exists_composition_triangle_lift p hp f g
    (SSet.yonedaEquiv.symm d.simplex) h₂ h₀
  refine ⟨e, t, ?_, ht⟩
  have h := congrArg (stdSimplex.δ (1 : Fin 3) ≫ ·) ht
  rw [← Category.assoc, SSet.Edge.CompStruct.δ_one_yonedaEquiv_symm,
    SSet.Edge.CompStruct.δ_one_yonedaEquiv_symm] at h
  exact h

end SerrePositivity.KST.Spectra
