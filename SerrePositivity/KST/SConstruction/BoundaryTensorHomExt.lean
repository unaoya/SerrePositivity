module
public import SerrePositivity.KST.SConstruction.AnodyneFixedHomotopy

/-! # 標準単体境界との直積上の全写像の等号判定
概要：境界と任意のパラメータの直積上の写像は、全余次元一面への制限で判定できる。
方針：パラメータを内部 Hom へ移し、元の標準境界の等号判定を使う。
規約：全パラメータを保ち、零単体だけの等号へ弱めない。
使われ方：実比較三角形の全境界を全高次比較時刻で固定する証明。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed BraidedCategory SSet
open scoped Simplicial

/-- 元の標準境界と全パラメータの直積上の写像を、全境界面で厳密に判定する。 -/
lemma boundaryTensorHomExt {n : ℕ} {K E : SSet.{u}}
    {f g : (∂Δ[n + 1] : SSet.{u}) ⊗ K ⟶ E}
    (h : ∀ i : Fin (n + 2), (SSet.boundary.ι i ▷ K) ≫ f =
      (SSet.boundary.ι i ▷ K) ≫ g) : f = g := by
  apply (cancel_epi (β_ K (∂Δ[n + 1] : SSet.{u})).hom).mp
  apply curry_injective
  apply SSet.boundary.hom_ext
  intro i
  rw [← curry_natural_left, ← curry_natural_left]
  apply congrArg curry
  rw [braiding_naturality_right_assoc, braiding_naturality_right_assoc]
  exact congrArg ((β_ K (Δ[n] : SSet.{u})).hom ≫ ·) (h i)

end SerrePositivity.KST.SConstruction
