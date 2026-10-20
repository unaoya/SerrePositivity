module
public import SerrePositivity.KST.SConstruction.AnodyneRelativeFibrationFamily

/-! # ホーンの全標準面による実写像の厳密な等号判定
概要：ホーン全体の実写像の等号を、全指定面の実写像の等号で判定する。
方針：標準面の Yoneda 表示から、元の全高次単体上の等号判定へ戻す。
規約：面の零頂点だけでなく全標準単体の写像を比較する。
使われ方：元の三合成面と指定全基底四面体を保つ相対持ち上げ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped Simplicial

/-- 全指定面の厳密な一致から、ホーン全体の全写像の一致を回収する。 -/
lemma hornHomExt {n : ℕ} (i : Fin (n + 2)) {E : SSet.{u}}
    {f g : (Λ[n + 1, i] : SSet.{u}) ⟶ E}
    (h : ∀ j (hj : j ≠ i), horn.ι i j hj ≫ f = horn.ι i j hj ≫ g) : f = g := by
  apply horn.hom_ext
  intro j hj
  have he := congrArg SSet.yonedaEquiv (h j hj)
  simpa only [SSet.yonedaEquiv_comp, horn.yonedaEquiv_ι] using he

end SerrePositivity.KST.SConstruction
