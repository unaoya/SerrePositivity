module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyUnit
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilySplitNaturality
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyPowerSplitAppend
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
模型。文献の定義との比較は後で
# 有限テンソルの生成射の最後の入力の分離

概要：Berger–Moerdijk §1 の作用の有限テンソルから最後の作用を分離する。
方針：既存の二ブロック分離の式へ、後半が一因子の場合の比較を適用する。
規約：最後の作用の出力には一次のテンソル冪の単位因子を補う。
使われ方：反復合成の評価の帰納段階で前半の作用と最後の作用を別々に計算する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

private lemma splitAtOne_coherence {C₀ : Type u} [Category.{v} C₀] [MonoidalCategory C₀]
    (U V : C₀) :
    ((ρ_ U).inv ▷ V) ≫ (α_ U (𝟙_ C₀) V).hom ≫
      (U ◁ ((λ_ V).hom ≫ (ρ_ V).inv)) = U ◁ (ρ_ V).inv := by
  simp only [whiskerLeft_comp]
  monoidal

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily _root_.SerrePositivity.TensorPowers.power
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：後半が一因子の分離は最後の分離の後に右単位因子を補う射である（Berger–Moerdijk §1）。
方針：二ブロック分離の後半長さ一の定義を展開し、単位子の整合性を使う。
規約：前半の末尾の単位因子と後半の右単位因子を区別する。
使われ方：既存の二ブロックの生成射の分離を最後の一因子の分離へ移す。 -/
lemma tensorFamilySplitAt_one_hom (n : ℕ) (V : Fin (n + 1) → Complex A) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitAt n 1 V).hom = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast n V).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => V j.castSucc) ◁ (ρ_ (V (Fin.last n))).inv) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitAt, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily, Iso.trans_hom, Iso.trans_inv,
    whiskerRightIso_hom, whiskerLeftIso_hom, Iso.symm_hom, Iso.symm_inv]
  erw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.splitAtOne_coherence (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => V j.castSucc)) (V (Fin.last n))]
  rfl

/-- 概要：有限作用族の最後の入力の分離は、前半の作用と最後の作用を連結した射になる（Berger–Moerdijk §1）。
方針：二ブロック分離の式へ後半が一因子の場合の比較を適用し、右単位子の自然性を使う。
規約：空の前半も含み、最後の出力に右単位因子を添える。
使われ方：最後の内側作用を代数の部分合成の評価へ適用する。 -/
lemma tensorFamilyGenerator_splitLast_inv {ι : Type} (X : Complex A) (D : ι → Complex A)
    (e : ∀ i, D i ⟶ X) (n : ℕ) (s : Fin (n + 1) → ι) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast n (fun j => D (s j))).inv ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator X D e (n + 1) s =
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator X D e n (fun j => s j.castSucc) ⊗ₘ e (s (Fin.last n))) ≫
      (power X n ◁ (ρ_ X).inv) ≫ (appendIso X n 1).hom := by
  have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator_splitToPower X D e n 1 s
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyPowerSplitIso_eq_append] at h
  have h' := congrArg (fun z => (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast n (fun j => D (s j))).inv ≫
    z ≫ (appendIso X n 1).hom) h
  simp only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id] at h'
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitAt_one_hom] at h'
  simp only [Category.assoc, Iso.inv_hom_id_assoc] at h'
  change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast n (fun j => D (s j))).inv ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator X D e (n + 1) s =
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => D (s j.castSucc)) ◁ (ρ_ (D (s (Fin.last n)))).inv) ≫
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator X D e n (fun j => s j.castSucc) ⊗ₘ
        (e (s (Fin.last n)) ⊗ₘ 𝟙 (𝟙_ (Complex A)))) ≫ (appendIso X n 1).hom at h'
  simp only [tensorHom_id] at h'
  rw [whiskerLeft_comp_tensorHom_assoc, ← rightUnitor_inv_naturality,
    ← tensorHom_comp_whiskerLeft] at h'
  exact h'

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
