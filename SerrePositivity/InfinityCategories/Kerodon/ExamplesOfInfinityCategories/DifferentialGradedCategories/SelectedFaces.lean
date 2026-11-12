module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornFaces

/-! # 選んだ面の和の単体と制限

概要：標準単体の任意に選んだ面の和で、面からの回収の選択独立性を示す。
方針：像が選んだ頂点を避けるという所属条件と、面による分解の自然性を使う。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：N7c の先頭の境界面からの回収。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaces

open CategoryTheory Opposite
open scoped _root_.Simplicial

/-- 概要：選んだ面の和は、選んだ頂点のいずれかを避ける単体からなる。
方針：所属を頂点の存在で定義し、前合成で回避条件が保たれることを使う。
規約：HA Proposition 1.3.1.10。使われ方：先頭の面だけを既知とする部分境界。 -/
def region {n : ℕ} (S : Finset (Fin (n + 1))) : (Δ[n] : SSet.{u}).Subcomplex where
  obj _ := {s | ∃ j ∈ S, ∀ k, SSet.stdSimplex.asOrderHom s k ≠ j}
  map α s hs := by
    obtain ⟨j, hj, h⟩ := hs
    exact ⟨j, hj, fun k => h (α.unop.toOrderHom k)⟩

/-- 概要：選んだ頂点を避ける順序写像は部分境界の単体になる。
方針：標準単体の順序写像表示に回避条件を添える。
規約：HA Proposition 1.3.1.10。使われ方：共通の制限の評価。 -/
def cell {m n : ℕ} (S : Finset (Fin (n + 1))) (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (j : Fin (n + 1)) (hjS : j ∈ S) (hj : ∀ k, θ.toOrderHom k ≠ j) :
    (region.{u} S : SSet) _⦋m⦌ :=
  ⟨SSet.stdSimplex.objEquiv.symm θ, j, hjS, hj⟩

/-- 概要：同じ順序写像による単体は避ける頂点の選択によらない。
方針：部分型の外延性を使う。
規約：HA Proposition 1.3.1.10。使われ方：回収時の面の選択独立性。 -/
lemma cell_eq {m n : ℕ} (S : Finset (Fin (n + 1))) (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (j l : Fin (n + 1)) (hjS : j ∈ S) (hlS : l ∈ S)
    (hj : ∀ k, θ.toOrderHom k ≠ j) (hl : ∀ k, θ.toOrderHom k ≠ l) :
    cell.{u} S θ j hjS hj = cell S θ l hlS hl := Subtype.ext rfl

/-- 概要：部分境界内の単体の制限は順序写像の前合成で得られる。
方針：標準単体の反変写像と部分型の外延性を使う。
規約：HA Proposition 1.3.1.10。使われ方：既知成分の制限との整合性。 -/
lemma map_cell {l m n : ℕ} (S : Finset (Fin (n + 1))) (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (j : Fin (n + 1)) (hjS : j ∈ S) (hj : ∀ k, θ.toOrderHom k ≠ j)
    (α : ⦋l⦌ ⟶ ⦋m⦌) :
    (region.{u} S : SSet).map α.op (cell S θ j hjS hj) =
      cell S (α ≫ θ) j hjS (fun k => hj (α.toOrderHom k)) := Subtype.ext rfl

/-- 概要：選んだ面そのものは部分境界の単体になる。
方針：面の順序写像が挿入位置を避けることを使う。
規約：HA Proposition 1.3.1.10。使われ方：面のデータの評価。 -/
def face {n : ℕ} (S : Finset (Fin (n + 2))) (j : Fin (n + 2)) (hjS : j ∈ S) :
    (region.{u} S : SSet) _⦋n⦌ := cell S (SimplexCategory.δ j) j hjS (Fin.succAbove_ne j)

/-- 概要：選んだ面への制限は対応する順序写像の単体と一致する。
方針：単体圏の面による分解を標準単体の値として評価する。
規約：HA Proposition 1.3.1.10。使われ方：任意の既知単体を面の制限として評価する。 -/
lemma map_face {m n : ℕ} (S : Finset (Fin (n + 2))) (θ : ⦋m⦌ ⟶ ⦋n + 1⦌)
    (j : Fin (n + 2)) (hjS : j ∈ S) (hj : ∀ k, θ.toOrderHom k ≠ j) :
    (region.{u} S : SSet).map (SimplexCategory.factor_δ θ j).op (face S j hjS) =
      cell S θ j hjS hj := by
  apply Subtype.ext
  change ULift.up (SimplexCategory.factor_δ θ j ≫ SimplexCategory.δ j) = ULift.up θ
  exact congrArg ULift.up (SimplexCategory.factor_δ_spec θ j hj)

/-- 概要：部分境界内の単体の像はそれを含む選んだ面の像の制限。
方針：写像の自然性を面の単体で評価し、面による分解を使う。
規約：HA Proposition 1.3.1.10。使われ方：dg nerve の既知成分を回収する。 -/
lemma restriction_from_face {m n : ℕ} {X : SSet.{u}}
    (S : Finset (Fin (n + 2))) (σ : (region S : SSet) ⟶ X)
    (θ : ⦋m⦌ ⟶ ⦋n + 1⦌) (j : Fin (n + 2)) (hjS : j ∈ S)
    (hj : ∀ k, θ.toOrderHom k ≠ j) :
    σ.app _ (cell S θ j hjS hj) =
      X.map (SimplexCategory.factor_δ θ j).op (σ.app _ (face S j hjS)) := by
  have h := congrArg (fun f => f (face S j hjS))
    (σ.naturality (SimplexCategory.factor_δ θ j).op)
  change σ.app _ ((region S : SSet).map (SimplexCategory.factor_δ θ j).op
    (face S j hjS)) = _ at h
  simpa only [map_face S θ j hjS hj, CategoryTheory.comp_apply] using h

/-- 概要：二つの選んだ面から回収する同じ単体の制限は等しい。
方針：どちらも同じ部分境界内の単体の像であることを使う。
規約：HA Proposition 1.3.1.10。使われ方：既知成分を回収する面の選択独立性。 -/
lemma restriction_independent {m n : ℕ} {X : SSet.{u}}
    (S : Finset (Fin (n + 2))) (σ : (region S : SSet) ⟶ X)
    (θ : ⦋m⦌ ⟶ ⦋n + 1⦌) (j l : Fin (n + 2)) (hjS : j ∈ S) (hlS : l ∈ S)
    (hj : ∀ k, θ.toOrderHom k ≠ j) (hl : ∀ k, θ.toOrderHom k ≠ l) :
    X.map (SimplexCategory.factor_δ θ j).op (σ.app _ (face S j hjS)) =
      X.map (SimplexCategory.factor_δ θ l).op (σ.app _ (face S l hlS)) := by
  rw [← restriction_from_face S σ θ j hjS hj, ← restriction_from_face S σ θ l hlS hl]
  exact congrArg (σ.app _) (cell_eq S θ j l hjS hlS hj hl)

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaces
