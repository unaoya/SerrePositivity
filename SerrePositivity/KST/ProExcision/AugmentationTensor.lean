module
public import SerrePositivity.HomologicalAlgebra.CochainTensor
public import Mathlib.Tactic.Abel
public import Mathlib.Algebra.Homology.Additive

/-!
# A.5 の右辺の augmentation 補正と次数評価

概要：非被約模型を保つ補正式のテンソル側を証明する。
方針：差のテンソルを双線形に展開し、各斉次成分の一方が零であることを使う。
規約：KST Construction A.5 の右辺の augmentation 補正。鎖次数は整数余鎖次数の符号を反転して読む。
使われ方：正規化後の低次数消滅を AW・shuffle の比較へ移す前の代数部分。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory MonoidalCategory HomologicalComplex
variable {R : Type u} [CommRing R]
variable {P P' Q Q' : CochainComplex (ModuleCat.{u} R) ℤ}

/-- 概要：二つの射の消滅次数の上界はテンソルで加算される。
方針：全複体の斉次直和への射の外延性を用い、一方の因子を零にする。
規約：KST Construction A.5 の整数余鎖模型。複体の項自体の消滅は要求しない。
使われ方：augmentation を引いた二射の低次数消滅を合成する。 -/
lemma tensorMap_eq_zero_above (f : P ⟶ P') (g : Q ⟶ Q') (a b : ℤ)
    (hf : ∀ i, a < i → f.f i = 0) (hg : ∀ j, b < j → g.f j = 0)
    (n : ℤ) (hn : a + b < n) : (cochainTensorMap f g).f n = 0 := by
  apply mapBifunctor.hom_ext
  intro i j hij
  change i + j = n at hij
  rw [ιTensorObj_cochainTensorMap]
  by_cases hi : a < i
  · simp [hf i hi]
  · simp [hg j (by omega)]

/-- 概要：augmentation を引いたテンソルの双線形展開。
方針：斉次直和上で whisker の加法性を使う。
規約：KST Construction A.5 の右辺の augmentation 補正。e と e' は各因子の定数射。
使われ方：差のテンソルの消滅から補正式を得る。 -/
lemma tensorMap_augmentation_expansion (f e : P ⟶ P') (g e' : Q ⟶ Q') :
    cochainTensorMap (f - e) (g - e') =
      cochainTensorMap f g - cochainTensorMap f e' -
        cochainTensorMap e g + cochainTensorMap e e' := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply mapBifunctor.hom_ext
  intro i j hij
  simp only [sub_f_apply, add_f_apply, Preadditive.comp_add, Preadditive.comp_sub,
    ιTensorObj_cochainTensorMap]
  simp only [tensorHom_def, sub_eq_add_neg, MonoidalPreadditive.add_whiskerRight,
    MonoidalPreadditive.whiskerLeft_add, Preadditive.add_comp, Preadditive.comp_add]
  have hnR : (-e.f i) ▷ Q.X j = -(e.f i ▷ Q.X j) :=
    (tensorRight (Q.X j)).map_neg
  have hnL : P'.X i ◁ (-e'.f j) = -(P'.X i ◁ e'.f j) :=
    (tensorLeft (P'.X i)).map_neg
  simp only [hnR, hnL, Preadditive.neg_comp, Preadditive.comp_neg, neg_neg]
  abel

/-- 概要：二つの差の消滅域の和で A.5 の補正式が成立する。
方針：差のテンソルを零化して双線形展開を移項する。
規約：KST Construction A.5 の右辺の augmentation 補正。非被約複体の通常の加減法。
使われ方：AW・shuffle と合成する成分等式。 -/
lemma tensorMap_augmentation_eq_above (f e : P ⟶ P') (g e' : Q ⟶ Q')
    (a b : ℤ) (hf : ∀ i, a < i → f.f i = e.f i)
    (hg : ∀ j, b < j → g.f j = e'.f j) (n : ℤ) (hn : a + b < n) :
    (cochainTensorMap f g).f n =
      (cochainTensorMap f e' + cochainTensorMap e g - cochainTensorMap e e').f n := by
  have hz := tensorMap_eq_zero_above (f - e) (g - e') a b
    (fun i hi ↦ by simp [hf i hi]) (fun j hj ↦ by simp [hg j hj]) n hn
  rw [tensorMap_augmentation_expansion] at hz
  simp only [sub_f_apply, add_f_apply] at hz ⊢
  apply sub_eq_zero.mp
  convert hz using 1
  abel

/-- 概要：鎖次数 m+m'+1 以下で補正式を得る。
方針：余鎖次数の上界を -m-1 と -m'-1 に取り、消滅域の加算を適用する。
規約：KST Construction A.5 の右辺の augmentation 補正。hf と hg は正規化後の差の消滅。
使われ方：A.5 の次数範囲を符号変換の誤りなく取り出す。 -/
lemma tensorMap_augmentation_eq_low (f e : P ⟶ P') (g e' : Q ⟶ Q')
    (m m' : ℕ) (hf : ∀ i : ℤ, -(m : ℤ) ≤ i → f.f i = e.f i)
    (hg : ∀ j : ℤ, -(m' : ℤ) ≤ j → g.f j = e'.f j)
    (n : ℕ) (hn : n ≤ m + m' + 1) :
    (cochainTensorMap f g).f (-(n : ℤ)) =
      (cochainTensorMap f e' + cochainTensorMap e g - cochainTensorMap e e').f
        (-(n : ℤ)) := by
  apply tensorMap_augmentation_eq_above f e g e' (-(m : ℤ) - 1) (-(m' : ℤ) - 1)
  · intro i hi
    exact hf i (by omega)
  · intro j hj
    exact hg j (by omega)
  · omega

end SerrePositivity.KST.ProExcision
