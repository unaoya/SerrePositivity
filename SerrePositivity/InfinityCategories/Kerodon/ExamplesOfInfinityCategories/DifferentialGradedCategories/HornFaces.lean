module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornIndex
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Computations

/-! # ホーンの面からの制限の回収

概要：ホーンに入る単体を利用可能な面を経由して評価し、面の選択によらないことを示す。
方針：単体圏の面による分解と、ホーンからの写像の自然性を使う。
規約：HA Proposition 1.3.1.10。使われ方：既知の部分集合の成分の整合した回収。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornFaces

open CategoryTheory Opposite
open scoped _root_.Simplicial

/-- 概要：欠けた面以外の頂点を一つ避ける単調写像はホーンの単体になる。
方針：避ける頂点が像に入らないことをホーンの所属条件に使う。
規約：HA Proposition 1.3.1.10。使われ方：部分集合の単体をホーン内で評価する。 -/
def cell {m n : ℕ} (i : Fin (n + 2)) (θ : ⦋m⦌ ⟶ ⦋n + 1⦌)
    (j : Fin (n + 2)) (hji : j ≠ i) (hj : ∀ k, θ.toOrderHom k ≠ j) :
    (Λ[n + 1, i] : SSet.{u}) _⦋m⦌ :=
  ⟨SSet.stdSimplex.objEquiv.symm θ,
    (SSet.mem_horn_iff_notMem_range _ i).mpr
      ⟨j, hji, fun ⟨k, hk⟩ => hj k hk⟩⟩

/-- 概要：同じ単調写像から得るホーンの単体は、避ける頂点の選択によらない。
方針：部分型の外延性と証明の一意性。
規約：HA Proposition 1.3.1.10。使われ方：面の選び方によらない回収。 -/
lemma cell_eq {m n : ℕ} (i : Fin (n + 2)) (θ : ⦋m⦌ ⟶ ⦋n + 1⦌)
    (j j' : Fin (n + 2)) (hji : j ≠ i) (hj'i : j' ≠ i)
    (hj : ∀ k, θ.toOrderHom k ≠ j) (hj' : ∀ k, θ.toOrderHom k ≠ j') :
    cell.{u} i θ j hji hj = cell i θ j' hj'i hj' := Subtype.ext rfl

/-- 概要：ホーン内の単体の制限は単調写像の前合成で得られる。
方針：標準単体の反変関手の定義と部分型の外延性。
規約：HA Proposition 1.3.1.10。使われ方：部分集合の包含と面の制限の整合性。 -/
lemma map_cell {l m n : ℕ} (i : Fin (n + 2)) (θ : ⦋m⦌ ⟶ ⦋n + 1⦌)
    (j : Fin (n + 2)) (hji : j ≠ i) (hj : ∀ k, θ.toOrderHom k ≠ j)
    (α : ⦋l⦌ ⟶ ⦋m⦌) :
    (Λ[n + 1, i] : SSet.{u}).map α.op (cell i θ j hji hj) =
      cell i (α ≫ θ) j hji (fun k => hj (α.toOrderHom k)) := Subtype.ext rfl

/-- 概要：像が j を避ける単体は、ホーンの j 面を経由する。
方針：`SimplexCategory.factor_δ_spec` の面による分解を標準単体へ移す。
規約：HA Proposition 1.3.1.10。使われ方：`horn.face` からの成分の回収。 -/
lemma map_face {m n : ℕ} (i : Fin (n + 2)) (θ : ⦋m⦌ ⟶ ⦋n + 1⦌)
    (j : Fin (n + 2)) (hji : j ≠ i) (hj : ∀ k, θ.toOrderHom k ≠ j) :
    (Λ[n + 1, i] : SSet.{u}).map (SimplexCategory.factor_δ θ j).op (SSet.horn.face i j hji) =
      cell i θ j hji hj := by
  apply Subtype.ext
  change ULift.up (SimplexCategory.factor_δ θ j ≫ SimplexCategory.δ j) = ULift.up θ
  exact congrArg ULift.up (SimplexCategory.factor_δ_spec θ j hj)

/-- 概要：ホーン内の単体の像は、任意の利用可能な面の像を制限して得られる。
方針：ホーンからの写像の自然性を面の単体で評価し、面による分解を使う。
規約：HA Proposition 1.3.1.10。使われ方：面のデータから既知の成分を取り出す。 -/
lemma restriction_from_face {m n : ℕ} {X : SSet.{u}}
    (i : Fin (n + 2)) (σ : (Λ[n + 1, i] : SSet.{u}) ⟶ X)
    (θ : ⦋m⦌ ⟶ ⦋n + 1⦌) (j : Fin (n + 2)) (hji : j ≠ i)
    (hj : ∀ k, θ.toOrderHom k ≠ j) :
    σ.app _ (cell i θ j hji hj) =
      X.map (SimplexCategory.factor_δ θ j).op (σ.app _ (SSet.horn.face i j hji)) := by
  have h := congrArg (fun f => f (SSet.horn.face i j hji))
    (σ.naturality (SimplexCategory.factor_δ θ j).op)
  change σ.app _ ((Λ[n + 1, i] : SSet.{u}).map (SimplexCategory.factor_δ θ j).op
      (SSet.horn.face i j hji)) = _ at h
  simpa only [map_face i θ j hji hj, CategoryTheory.comp_apply] using h

/-- 概要：二つの利用可能な面から回収する同じ単体の制限は一致する。
方針：どちらもホーン内の同じ単体の像に等しいことを自然性から得る。
規約：HA Proposition 1.3.1.10。使われ方：斉次成分の回収の選択独立性。 -/
lemma restriction_independent {m n : ℕ} {X : SSet.{u}}
    (i : Fin (n + 2)) (σ : (Λ[n + 1, i] : SSet.{u}) ⟶ X)
    (θ : ⦋m⦌ ⟶ ⦋n + 1⦌) (j j' : Fin (n + 2)) (hji : j ≠ i) (hj'i : j' ≠ i)
    (hj : ∀ k, θ.toOrderHom k ≠ j) (hj' : ∀ k, θ.toOrderHom k ≠ j') :
    X.map (SimplexCategory.factor_δ θ j).op (σ.app _ (SSet.horn.face i j hji)) =
      X.map (SimplexCategory.factor_δ θ j').op (σ.app _ (SSet.horn.face i j' hj'i)) := by
  rw [← restriction_from_face i σ θ j hji hj, ← restriction_from_face i σ θ j' hj'i hj']
  exact congrArg (σ.app _) (cell_eq i θ j j' hji hj'i hj hj')

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornFaces
