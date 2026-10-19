module

public import SerrePositivity.KST.Spectra.CompositionTriangleSquare
public import SerrePositivity.KST.Spectra.BoundaryTensorExt

/-!
概要：恒等辺を第一辺に持つ実三角形から、残り二辺の両端固定ホモトピーを構成する。
方針：同じ三角形から得る正方形の左右の辺を、元の二つの頂点での定数辺へ照合する。
規約：標的の Kan 性は不要。使われ方：区間列の構造比較の相対条件。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra

/-- 恒等辺を単体写像へ戻すと、同じ頂点の定数写像になる。 -/
lemma edgeId_yonedaEquiv_symm {E : SSet.{u}} (x : E _⦋0⦌) :
    SSet.yonedaEquiv.symm (SSet.Edge.id x).edge = SSet.const x := by
  have h := congrArg (fun e : E.Edge x x ↦ SSet.yonedaEquiv.symm e.edge)
    (FundamentalLoop.edge_const (X := E) (x := x))
  change SSet.yonedaEquiv.symm (SSet.yonedaEquiv (SSet.const x)) =
    SSet.yonedaEquiv.symm (SSet.Edge.id x).edge at h
  rw [Equiv.symm_apply_apply] at h
  exact h.symm

variable {E : SSet.{u}} {x y z : E _⦋0⦌}
  {a : E.Edge x y} {b : E.Edge y z} {c : E.Edge x z}
  (t : SSet.Edge.CompStruct a b c)

/-- 元の三角形から得る正方形は、元の二つの端点を全区間で厳密に固定する。 -/
lemma compositionTriangleHomotopy_boundary_of_const
    (ha : SSet.yonedaEquiv.symm a.edge = SSet.const x) :
    (boundary 1).ι ▷ (Δ[1] : SSet.{u}) ≫ (compositionTriangleHomotopy t).h =
      fst (∂Δ[1] : SSet.{u}) (Δ[1] : SSet.{u}) ≫
        (boundary 1).ι ≫ SSet.yonedaEquiv.symm c.edge := by
  change (boundary 1).ι ▷ (Δ[1] : SSet.{u}) ≫ compositionTriangleSquare t =
    fst (∂Δ[1] : SSet.{u}) (Δ[1] : SSet.{u}) ≫
      (boundary 1).ι ≫ SSet.yonedaEquiv.symm c.edge
  apply boundary_tensor_hom_ext
  intro i
  simp only [← comp_whiskerRight_assoc, boundary.ι_ι, whiskerRight_fst_assoc,
    boundary.ι_ι_assoc]
  fin_cases i
  · change stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u}) ≫ compositionTriangleSquare t =
      fst (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫
        stdSimplex.δ (0 : Fin 2) ≫ SSet.yonedaEquiv.symm c.edge
    rw [compositionTriangleSquare_finish, SSet.Edge.δ_zero_yonedaEquiv_symm,
      edgeId_yonedaEquiv_symm, SSet.yonedaEquiv_symm_zero, SSet.comp_const, SSet.comp_const]
  · change stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u}) ≫ compositionTriangleSquare t =
      fst (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫
        stdSimplex.δ (1 : Fin 2) ≫ SSet.yonedaEquiv.symm c.edge
    rw [compositionTriangleSquare_start, SSet.Edge.δ_one_yonedaEquiv_symm,
      ha, SSet.yonedaEquiv_symm_zero, SSet.comp_const, SSet.comp_const]

/-- 第一辺が恒等辺の三角形では、両端固定の同じ区間ホモトピーが得られる。 -/
lemma identityTriangleHomotopy_boundary {E : SSet.{u}} {x z : E _⦋0⦌}
    {b c : E.Edge x z} (t : SSet.Edge.CompStruct (SSet.Edge.id x) b c) :
    (boundary 1).ι ▷ (Δ[1] : SSet.{u}) ≫ (compositionTriangleHomotopy t).h =
      fst (∂Δ[1] : SSet.{u}) (Δ[1] : SSet.{u}) ≫
        (boundary 1).ι ≫ SSet.yonedaEquiv.symm c.edge :=
  compositionTriangleHomotopy_boundary_of_const t (edgeId_yonedaEquiv_symm x)

end SerrePositivity.KST.Spectra
