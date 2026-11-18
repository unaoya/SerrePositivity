module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilySplitAtNaturality
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyUnit

/-!
模型。文献の定義との比較は後で
# 先頭演算と後半の演算族を一つの有限テンソルへ組み込む

概要：Berger–Moerdijk §1 の二段の全合成で先頭演算を外側の入力族へ入れる。
方針：先頭に単位因子を付け、二ブロック分離の逆射で全体を再結合する。
規約：先頭の添字は Fin 1 の castAdd、後半の添字は natAdd 1。
使われ方：係数列と入力列の両方で先頭ブロックの合成結果を組み込む。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：先頭の因子と後半の有限テンソルから全入力の有限テンソルへ送る（Berger–Moerdijk §1）。
方針：先頭因子の右に単位を付けて一入力の有限テンソルにし、分離の逆射を使う。
規約：後半は空でもよい。
使われ方：先頭ブロックを一つの演算にまとめた後の入力族を構成する。 -/
def tensorFamilyHeadAssembly (m : ℕ) (V : Fin (1 + m) → Complex A) :
    V ((0 : Fin 1).castAdd m) ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily m (fun j => V (j.natAdd 1)) ⟶
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (1 + m) V :=
  ((ρ_ (V ((0 : Fin 1).castAdd m))).inv ▷ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily m (fun j => V (j.natAdd 1))) ≫
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitAt 1 m V).inv

/-- 概要：先頭の組み込みは各因子の射に関して自然である（Berger–Moerdijk §1）。
方針：右単位子の自然性と二ブロックの再結合の自然性を使う。
規約：先頭と後半の射を独立に指定する。
使われ方：先頭に合成した生成射を Schur 入力の生成射へ移す。 -/
lemma tensorFamilyHeadAssembly_naturality (m : ℕ) {V W : Fin (1 + m) → Complex A}
    (f : ∀ j, V j ⟶ W j) :
    (f ((0 : Fin 1).castAdd m) ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap m (fun j => f (j.natAdd 1))) ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyHeadAssembly m W =
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyHeadAssembly m V ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap (1 + m) f := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyHeadAssembly
  rw [Category.assoc, tensorHom_comp_whiskerRight_assoc]
  rw [rightUnitor_inv_naturality]
  rw [← whiskerRight_comp_tensorHom_assoc]
  have hn := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitAt_inv_naturality 1 m f
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap, tensorHom_id] at hn
  erw [hn]

/-- 概要：先頭一入力の係数・入力の分離は逆の単位子と両立する（Berger–Moerdijk §1）。
方針：一次の分離の単位則に逆射を前後から合成して相殺する。
規約：始域には単位因子を含めない。
使われ方：先頭を組み込む射の係数と入力を分離する。 -/
lemma tensorFamilyTensorIso_one_inv (V W : Fin 1 → Complex A) :
    (ρ_ (V 0 ⊗ W 0)).inv ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso 1 V W).hom =
      ((ρ_ (V 0)).inv ⊗ₘ (ρ_ (W 0)).inv) := by
  apply (cancel_mono ((ρ_ (V 0)).hom ⊗ₘ (ρ_ (W 0)).hom)).1
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso_one]
  simp only [Iso.inv_hom_id, tensorHom_comp_tensorHom, tensorHom_id, id_whiskerRight]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
