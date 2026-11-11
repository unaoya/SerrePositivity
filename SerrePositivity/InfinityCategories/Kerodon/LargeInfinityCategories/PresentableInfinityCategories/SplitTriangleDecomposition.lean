module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone
public import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct

/-!
概要：恒等長辺を持つ実二単体を、同じ基点で始終する分裂合成構造へ分解する。
方針：三つの標準頂点の面関係で両辺の端点を回収する。
規約：元の二単体の値は厳密に保持する。
使われ方：前置 coslice の持ち上げた三角形を余錐拡張へ渡す。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：恒等長辺を持つ二単体は、同じ元の頂点の分裂三角形となる。
方針：始点・中点・終点の二通りの顔の制限を比較する。
規約：元の二単体そのものを合成構造の単体にする。
使われ方：全交互前置図式の分裂比較の回収。 -/
lemma exists_splitCompStruct_of_identity_longEdge {X : SSet.{u}}
    (x : X _⦋0⦌) (S : X _⦋2⦌) (hS : X.δ 1 S = (SSet.Edge.id x).edge) :
    ∃ (y : X _⦋0⦌) (e : X.Edge x y) (r : X.Edge y x)
      (T : e.CompStruct r (SSet.Edge.id x)), T.simplex = S := by
  let U := SSet.yonedaEquiv.symm S
  have hs : X.δ 1 (X.δ 2 S) = X.δ 1 (X.δ 1 S) := by
    have h : (SSet.stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) ≫
        SSet.stdSimplex.δ (2 : Fin 3) =
      SSet.stdSimplex.δ (1 : Fin 2) ≫ SSet.stdSimplex.δ (1 : Fin 3) := by
      apply SSet.yonedaEquiv.injective
      decide
    have h' := congrArg (fun f ↦ SSet.yonedaEquiv (f ≫ U)) h
    simpa only [Category.assoc, SSet.stdSimplex.yonedaEquiv_δ_comp,
      U, Equiv.apply_symm_apply] using h'
  have ht : X.δ 0 (X.δ 0 S) = X.δ 0 (X.δ 1 S) := by
    have h : (SSet.stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) ≫
        SSet.stdSimplex.δ (0 : Fin 3) =
      SSet.stdSimplex.δ (0 : Fin 2) ≫ SSet.stdSimplex.δ (1 : Fin 3) := by
      apply SSet.yonedaEquiv.injective
      decide
    have h' := congrArg (fun f ↦ SSet.yonedaEquiv (f ≫ U)) h
    simpa only [Category.assoc, SSet.stdSimplex.yonedaEquiv_δ_comp,
      U, Equiv.apply_symm_apply] using h'
  have hm : X.δ 1 (X.δ 0 S) = X.δ 0 (X.δ 2 S) := by
    have h : (SSet.stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) ≫
        SSet.stdSimplex.δ (0 : Fin 3) =
      SSet.stdSimplex.δ (0 : Fin 2) ≫ SSet.stdSimplex.δ (2 : Fin 3) := by
      apply SSet.yonedaEquiv.injective
      decide
    have h' := congrArg (fun f ↦ SSet.yonedaEquiv (f ≫ U)) h
    simpa only [Category.assoc, SSet.stdSimplex.yonedaEquiv_δ_comp,
      U, Equiv.apply_symm_apply] using h'
  have hsrc : X.δ 1 (X.δ 2 S) = x := by
    rw [hs, hS]
    exact (SSet.Edge.id x).src_eq
  have htgt : X.δ 0 (X.δ 0 S) = x := by
    rw [ht, hS]
    exact (SSet.Edge.id x).tgt_eq
  let e : X.Edge x (X.δ 0 (X.δ 2 S)) := SSet.Edge.mk (X.δ 2 S) hsrc rfl
  let r : X.Edge (X.δ 0 (X.δ 2 S)) x := SSet.Edge.mk (X.δ 0 S) hm htgt
  exact ⟨_, e, r, SSet.Edge.CompStruct.mk S rfl rfl hS, rfl⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
