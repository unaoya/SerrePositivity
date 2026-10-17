module
public import SerrePositivity.InfinityCategories.DGNerve.PinchedHornFilling
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex

/-! # dg nerve の右 pinched 写像空間の Kan 性

概要：任意の可換環上の dg 圏の右 pinched 写像空間は Kan 複体。
方針：全頂点削除方程式の直接の線形充填を実際の単体に戻し、面の一致で貼り合わせる。
規約：Kerodon §4.6.5、N0.3。使われ方：写像空間の連結成分と H⁰ の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.DGNerve.PinchedHom

open CategoryTheory Opposite DifferentialGraded
open scoped Simplicial

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {x y : D}

/-- 概要：任意の右 pinched ホーンの実際の充填単体。
方針：直接の線形充填を全次数の比較の逆写像で単体に戻す。
規約：Kerodon §4.6.5。使われ方：ホーンから標準単体への延長。 -/
def filler {n : ℕ} {i : Fin (n + 2)}
    (σ : (Λ[n + 1, i] : SSet.{max u v}) ⟶ DGNerve.pinchedHom A D x y) :
    (DGNerve.pinchedHom A D x y) _⦋n + 1⦌ := (HornData.filler σ).toPinched

/-- 概要：充填単体の各利用可能な面は元のホーン面と一致する。
方針：線形表示の単射性・自然性・両逆則と、充填族の面の計算を使う。
規約：Kerodon §4.6.5。使われ方：米田対応によるホーンの貼合せ。 -/
lemma filler_face {n : ℕ} {i : Fin (n + 2)}
    (σ : (Λ[n + 1, i] : SSet.{max u v}) ⟶ DGNerve.pinchedHom A D x y)
    (j : Fin (n + 2)) (hji : j ≠ i) :
    (DGNerve.pinchedHom A D x y).δ j (filler σ) = σ.app _ (SSet.horn.face i j hji) := by
  apply (linearEquiv x y n).injective
  change toLinearSimplex ((filler σ).pullback (SimplexCategory.δ j)) = _
  rw [toLinearSimplex_pullback]
  apply Subtype.ext
  change LinearData.pullback (SimplexCategory.δ j).toOrderHom (toLinearData (filler σ)) =
    HornData.faceData σ j hji
  have he : toLinearData (filler σ) = (HornData.filler σ).val :=
    congrArg Subtype.val (LinearSimplex.toLinearSimplex_toPinched (HornData.filler σ))
  rw [he]
  exact HornData.fillerData_pullback_face σ j hji

/-- 概要：任意の右 pinched ホーン写像は標準単体全体へ延長できる。
方針：直接の線形充填単体を米田対応で写像にし、各面の一致からホーンの外延性を使う。
規約：Kerodon §4.6.5。使われ方：Mathlib の Kan 条件の充足。 -/
lemma hornFilling {n : ℕ} {i : Fin (n + 2)}
    (σ : (Λ[n + 1, i] : SSet.{max u v}) ⟶ DGNerve.pinchedHom A D x y) :
    ∃ τ : (Δ[n + 1] : SSet.{max u v}) ⟶ DGNerve.pinchedHom A D x y,
      σ = Λ[n + 1, i].ι ≫ τ := by
  refine ⟨SSet.yonedaEquiv.symm (filler σ), ?_⟩
  apply SSet.horn.hom_ext
  intro j hji
  rw [← filler_face σ j hji, NatTrans.comp_app]
  rfl

/-- 概要：任意の可換環上の dg 圏の右 pinched 写像空間は Kan 複体。
方針：全ホーン番号で線形充填を与え、Mathlib のホーンによる特徴づけを使う。
規約：Kerodon §4.6.5。使われ方：写像空間のホモトピー型と連結成分の比較。 -/
instance instKanComplex : SSet.KanComplex (DGNerve.pinchedHom A D x y) := by
  rw [SSet.KanComplex.iff]
  intro n i f hf
  obtain ⟨τ, hτ⟩ := hornFilling hf.desc
  refine ⟨τ, fun j hj => ?_⟩
  rw [← SSet.horn.ι_ι i j hj, Category.assoc, ← hτ]
  exact hf.ι_desc j hj

end SerrePositivity.InfinityCategories.DGNerve.PinchedHom
