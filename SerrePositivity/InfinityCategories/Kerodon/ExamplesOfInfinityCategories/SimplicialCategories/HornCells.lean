module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.HornData

/-!
# ホーン内の単体と面の選択によらない制限

概要：ホーン内の同じ単体を異なる既知面から評価した結果は一致する。
方針：標準単体の面による因子分解と単体的写像の自然性を使う。
規約：一般の単体集合への写像に対して証明し、dg nerve に依存しない。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の零座標面の重なりの比較。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section

universe w v u

open CategoryTheory Opposite
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

/-- 概要：欠けた面以外の頂点を一つ避ける単調写像はホーンの単体になる。
方針：避ける頂点が像に入らないことをホーンの所属条件に使う。
規約：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）。使われ方：部分集合の単体をホーン内で評価する。 -/
def hornCell {m n : ℕ} (i : Fin (n + 2)) (θ : ⦋m⦌ ⟶ ⦋n + 1⦌)
    (j : Fin (n + 2)) (hji : j ≠ i) (hj : ∀ k, θ.toOrderHom k ≠ j) :
    (Λ[n + 1, i] : SSet.{w}) _⦋m⦌ :=
  ⟨SSet.stdSimplex.objEquiv.symm θ,
    (SSet.mem_horn_iff_notMem_range _ i).mpr
      ⟨j, hji, fun ⟨k, hk⟩ => hj k hk⟩⟩

/-- 概要：同じ単調写像から得るホーンの単体は、避ける頂点の選択によらない。
方針：部分型の外延性と証明の一意性。
規約：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）。使われ方：面の選び方によらない回収。 -/
lemma hornCell_eq {m n : ℕ} (i : Fin (n + 2)) (θ : ⦋m⦌ ⟶ ⦋n + 1⦌)
    (j j' : Fin (n + 2)) (hji : j ≠ i) (hj'i : j' ≠ i)
    (hj : ∀ k, θ.toOrderHom k ≠ j) (hj' : ∀ k, θ.toOrderHom k ≠ j') :
    hornCell.{w} i θ j hji hj = hornCell i θ j' hj'i hj' := Subtype.ext rfl

/-- 概要：ホーン内の単体の制限は単調写像の前合成で得られる。
方針：標準単体の反変関手の定義と部分型の外延性。
規約：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）。使われ方：部分集合の包含と面の制限の整合性。 -/
lemma hornCell_map {l m n : ℕ} (i : Fin (n + 2)) (θ : ⦋m⦌ ⟶ ⦋n + 1⦌)
    (j : Fin (n + 2)) (hji : j ≠ i) (hj : ∀ k, θ.toOrderHom k ≠ j)
    (α : ⦋l⦌ ⟶ ⦋m⦌) :
    (Λ[n + 1, i] : SSet.{w}).map α.op (hornCell i θ j hji hj) =
      hornCell i (α ≫ θ) j hji (fun k => hj (α.toOrderHom k)) := Subtype.ext rfl

/-- 概要：像が j を避ける単体は、ホーンの j 面を経由する。
方針：`SimplexCategory.factor_δ_spec` の面による分解を標準単体へ移す。
規約：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）。使われ方：`horn.face` からの成分の回収。 -/
lemma hornCell_from_face {m n : ℕ} (i : Fin (n + 2)) (θ : ⦋m⦌ ⟶ ⦋n + 1⦌)
    (j : Fin (n + 2)) (hji : j ≠ i) (hj : ∀ k, θ.toOrderHom k ≠ j) :
    (Λ[n + 1, i] : SSet.{w}).map (SimplexCategory.factor_δ θ j).op (SSet.horn.face i j hji) =
      hornCell i θ j hji hj := by
  apply Subtype.ext
  change ULift.up (SimplexCategory.factor_δ θ j ≫ SimplexCategory.δ j) = ULift.up θ
  exact congrArg ULift.up (SimplexCategory.factor_δ_spec θ j hj)

set_option backward.isDefEq.respectTransparency false in
/-- 概要：ホーン内の単体の像は、任意の利用可能な面の像を制限して得られる。
方針：ホーンからの写像の自然性を面の単体で評価し、面による分解を使う。
規約：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）。使われ方：面のデータから既知の成分を取り出す。 -/
lemma hornRestriction_from_face {m n : ℕ} {X : SSet.{w}}
    (i : Fin (n + 2)) (σ : (Λ[n + 1, i] : SSet.{w}) ⟶ X)
    (θ : ⦋m⦌ ⟶ ⦋n + 1⦌) (j : Fin (n + 2)) (hji : j ≠ i)
    (hj : ∀ k, θ.toOrderHom k ≠ j) :
    σ.app _ (hornCell i θ j hji hj) =
      X.map (SimplexCategory.factor_δ θ j).op (σ.app _ (SSet.horn.face i j hji)) := by
  have h := congrArg (fun f => f (SSet.horn.face i j hji))
    (σ.naturality (SimplexCategory.factor_δ θ j).op)
  change σ.app _ ((Λ[n + 1, i] : SSet.{w}).map (SimplexCategory.factor_δ θ j).op
      (SSet.horn.face i j hji)) = _ at h
  simpa only [hornCell_from_face i θ j hji hj, CategoryTheory.comp_apply] using h

/-- 概要：二つの利用可能な面から回収する同じ単体の制限は一致する。
方針：どちらもホーン内の同じ単体の像に等しいことを自然性から得る。
規約：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）。使われ方：Hom データの回収の選択独立性。 -/
lemma hornRestriction_independent {m n : ℕ} {X : SSet.{w}}
    (i : Fin (n + 2)) (σ : (Λ[n + 1, i] : SSet.{w}) ⟶ X)
    (θ : ⦋m⦌ ⟶ ⦋n + 1⦌) (j j' : Fin (n + 2)) (hji : j ≠ i) (hj'i : j' ≠ i)
    (hj : ∀ k, θ.toOrderHom k ≠ j) (hj' : ∀ k, θ.toOrderHom k ≠ j') :
    X.map (SimplexCategory.factor_δ θ j).op (σ.app _ (SSet.horn.face i j hji)) =
      X.map (SimplexCategory.factor_δ θ j').op (σ.app _ (SSet.horn.face i j' hj'i)) := by
  rw [← hornRestriction_from_face i σ θ j hji hj, ← hornRestriction_from_face i σ θ j' hj'i hj']
  exact congrArg (σ.app _) (hornCell_eq i θ j j' hji hj'i hj hj')

variable {C : Type u} [Category.{v} C] [SimplicialCategory C]

/-- 概要：ホーン内の単体の Hom 写像を、その全体の頂点対象の間で回収する。
方針：避ける頂点からホーンの単体を作り、既存の Hom 回収を適用する。
規約：θ の像が既知面 j に入ることだけを仮定する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の共通面上の Hom 写像。 -/
def hornCellHom {m n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (θ : ⦋m⦌ ⟶ ⦋n + 2⦌) (j : Fin (n + 3)) (hj : j ≠ i)
    (hθ : ∀ k, θ.toOrderHom k ≠ j) (a b : Fin (m + 1)) :
    nerve (SimplicialThickening.Path (ULift.up.{v} a) (ULift.up.{v} b)) ⟶
      SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ (θ.toOrderHom a)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ (θ.toOrderHom b)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomOnCell σ (hornCell i θ j hj hθ) a b

/-- 概要：同じ単体の Hom 回収は、避ける頂点の選択によらず厳密に一致する。
方針：ホーンの単体のデータは θ だけで、所属の証明は一意である。
規約：両方の面がホーンに含まれることを明示する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の零座標面の重なり。 -/
lemma hornCellHom_independent {m n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (θ : ⦋m⦌ ⟶ ⦋n + 2⦌) (j k : Fin (n + 3)) (hj : j ≠ i) (hk : k ≠ i)
    (hθj : ∀ a, θ.toOrderHom a ≠ j) (hθk : ∀ a, θ.toOrderHom a ≠ k)
    (a b : Fin (m + 1)) :
    hornCellHom σ θ j hj hθj a b = hornCellHom σ θ k hk hθk a b := rfl

/-- 概要：回収した共通単体の Hom 写像は、任意の既知面の制限の Hom 写像と異種等号で一致する。
方針：ホーンの自然性による enriched functor の等式を Hom で評価して移送を消去する。
規約：右辺は Mathlib の SimplicialNerve の実際の制限である。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の零座標面の重なりの比較。 -/
lemma hornCellHom_from_face_heq {m n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (θ : ⦋m⦌ ⟶ ⦋n + 2⦌) (j : Fin (n + 3)) (hj : j ≠ i)
    (hθ : ∀ k, θ.toOrderHom k ≠ j) (a b : Fin (m + 1)) :
    HEq (hornCellHom σ θ j hj hθ a b)
      (((SimplicialNerve C).map (SimplexCategory.factor_δ θ j).op
        (σ.app _ (SSet.horn.face i j hj))).map ⟨⟨a⟩⟩ ⟨⟨b⟩⟩) := by
  have hF := hornRestriction_from_face i σ θ j hj hθ
  have hm (F G : EnrichedFunctor SSet
      (SimplicialThickening (ULift.{v} (Fin (m + 1)))) C) (h : F = G) :
      HEq (F.map ⟨⟨a⟩⟩ ⟨⟨b⟩⟩) (G.map ⟨⟨a⟩⟩ ⟨⟨b⟩⟩) := by
    subst G
    rfl
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomOnCell_heq σ _ a b).trans (hm _ _ hF)

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
