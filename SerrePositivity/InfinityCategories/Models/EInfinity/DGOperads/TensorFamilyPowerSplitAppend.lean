module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyPowerOnes
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyPowerSplitTransport

/-!
模型。文献の定義との比較は後で
# 有限族由来のテンソル冪の分離と標準の連結同型

概要：Berger–Moerdijk §1 の先頭の入力射で用いる二つの分離同型を比較する。
方針：一次のブロックの生成射上で比較し、二ブロック連結との両立を使う。
規約：入力の長さは n+m、出力は n と m のテンソル冪。
使われ方：補助的な先頭入力射を既存のテンソル代入射に同定する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers
open scoped _root_.BigOperators

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：標準の連結は両方の入力長の等式による移送と両立する（Berger–Moerdijk §1）。
方針：入力長の等式を消去し、恒等射のテンソルを簡約する。
規約：両方の長さを独立に移送する。
使われ方：一次の有限族の総 arity を入力数へ移す。 -/
lemma appendIso_index_pair (X : Complex A) {n n' m m' : ℕ} (hn : n = n') (hm : m = m') :
    (eqToHom (congrArg (power X) hn) ⊗ₘ eqToHom (congrArg (power X) hm)) ≫
      (appendIso X n' m').hom =
    (appendIso X n m).hom ≫ eqToHom (congrArg (power X) (congrArg₂ (· + ·) hn hm)) := by
  subst n'
  subst m'
  simp only [eqToHom_refl, tensorHom_id, id_whiskerRight, Category.id_comp, Category.comp_id]

/-- 概要：有限族から移した分離の後に標準の連結を行うと恒等射となる（Berger–Moerdijk §1）。
方針：一次のテンソル冪の生成射を前置し、生成射の分離則と二ブロックの連結則を比較する。
規約：空の前半と後半を含む。
使われ方：有限族由来の分離を標準の連結の逆射へ同定する。 -/
lemma tensorFamilyPowerSplitIso_append (X : Complex A) (n m : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyPowerSplitIso X n m).hom ≫ (appendIso X n m).hom =
      𝟙 (power X (n + m)) := by
  let G := fun k => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator X (fun _ : ℕ => power X 1)
    (fun _ => (ρ_ X).hom) k (fun _ => 1)
  have hG (k : ℕ) : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso X k (fun _ => 1)).hom ≫
      eqToHom (congrArg (power X) (by simp : (∑ _ : Fin k, 1) = k)) = G k :=
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso_ones X k
  have : IsIso (G (n + m)) := by
    rw [← hG]
    infer_instance
  apply (cancel_epi (G (n + m))).1
  dsimp only [G]
  simp only [Category.comp_id]
  rw [reassoc_of% (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator_splitToPower X (fun _ : ℕ => power X 1)
    (fun _ => (ρ_ X).hom) n m (fun _ => 1))]
  rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso_ones X n, ← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso_ones X m,
    ← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso_ones X (n + m)]
  rw [← tensorHom_comp_tensorHom]
  simp only [Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.appendIso_index_pair X (by simp : (∑ _ : Fin n, 1) = n)
    (by simp : (∑ _ : Fin m, 1) = m)]
  have h := congrArg (· ≫ eqToHom (congrArg (power X)
    (by simp : (∑ _ : Fin (n + m), 1) = n + m)))
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso_splitAt X n m (fun _ => 1))
  simp only [Category.assoc, eqToHom_trans] at h
  exact h

/-- 概要：有限族由来のテンソル冪の分離は標準の連結同型の逆同型である（Berger–Moerdijk §1）。
方針：連結射を後置して射を比較し、同型の逆射の一意性を使う。
規約：同型そのものの等式として保持する。
使われ方：先頭入力射の定義を既存の appendIso の式へ移す。 -/
lemma tensorFamilyPowerSplitIso_eq_append (X : Complex A) (n m : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyPowerSplitIso X n m = (appendIso X n m).symm := by
  apply Iso.ext
  apply (cancel_mono (appendIso X n m).hom).1
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyPowerSplitIso_append]
  simp only [Iso.symm_hom, Iso.inv_hom_id]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
