module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorNaturality
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
模型。文献の定義との比較は後で
# テンソル単位の反復テンソル

概要：Berger–Fresse §3.1 の単位余代数の出力を標準のテンソル単位と比較する。
方針：右括弧の反復テンソルを先頭から縮約する。
規約：零重テンソルの縮約は恒等同型である。
使われ方：augmentation に付随する単位余代数と区間の端点条件を定義する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.TensorPowers

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]

/-- 概要：単位対象の n 重テンソルを単位へ縮約する同型（BF §3.1）。
方針：尾を再帰的に縮約し左単位子を適用する。
規約：n=0 の縮約は恒等同型。
使われ方：単位余代数の余演算の終域を供給する。 -/
def tensorUnitPowerIso : ∀ n : ℕ, power (𝟙_ C) n ≅ 𝟙_ C
  | 0 => Iso.refl _
  | n + 1 => whiskerLeftIso (𝟙_ C) (tensorUnitPowerIso n) ≪≫ λ_ (𝟙_ C)

/-- 概要：単位の一次冪の縮約は既存の一次冪の比較と一致する（BF §3.1）。
方針：左右の単位子の単位対象上での一致を使う。
規約：同型の順方向の射の等式とする。
使われ方：単位余代数の単位則を証明する。 -/
lemma tensorUnitPowerIso_one : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitPowerIso C 1).hom = (oneIso (𝟙_ C)).hom := by
  change ((𝟙_ C) ◁ 𝟙 (𝟙_ C)) ≫ (λ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom
  simp only [whiskerLeft_id, Category.id_comp, unitors_equal]


/-- 概要：単位冪の縮約は arity の等式による移送を消去する（BF §3.1）。
方針：等式を帰納して恒等射へ帰着する。
規約：移送前後のテンソル単位は同一。
使われ方：単位余演算の出力数の算術的な表示を揃える。 -/
@[reassoc]
lemma tensorUnitPowerIso_index {m n : ℕ} (h : m = n) :
    eqToHom (congrArg (power (𝟙_ C)) h) ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitPowerIso C n).hom =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitPowerIso C m).hom := by
  subst n
  simp only [eqToHom_refl, Category.id_comp]

/-- 概要：単位冪の連結と縮約は両列の縮約に一致する（BF §3.1）。
方針：前半の長さで帰納し、結合子と単位子の整合性を使う。
規約：空の列も含む。
使われ方：単位余代数の部分合成則に現れる出力列を縮約する。 -/
lemma tensorUnitPowerIso_append (m n : ℕ) :
    (appendIso (𝟙_ C) m n).hom ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitPowerIso C (m + n)).hom =
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitPowerIso C m).hom ⊗ₘ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitPowerIso C n).hom) ≫
        (λ_ (𝟙_ C)).hom := by
  induction m with
  | zero =>
    simp only [appendIso, Iso.trans_hom, eqToIso.hom, Category.assoc]
    erw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitPowerIso_index C (Nat.zero_add n).symm]
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitPowerIso, Iso.refl_hom, id_tensorHom]
    exact (leftUnitor_naturality (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitPowerIso C n).hom).symm
  | succ m ih =>
    rw [appendIso]
    simp only [Iso.trans_hom, whiskerLeftIso_hom, eqToIso.hom, Category.assoc]
    erw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitPowerIso_index C (Nat.succ_add m n).symm]
    change (α_ (𝟙_ C) (power (𝟙_ C) m) (power (𝟙_ C) n)).hom ≫
      ((𝟙_ C) ◁ (appendIso (𝟙_ C) m n).hom) ≫
      ((𝟙_ C) ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitPowerIso C (m + n)).hom) ≫ (λ_ (𝟙_ C)).hom =
      ((((𝟙_ C) ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitPowerIso C m).hom) ≫ (λ_ (𝟙_ C)).hom) ⊗ₘ
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitPowerIso C n).hom) ≫ (λ_ (𝟙_ C)).hom
    rw [← whiskerLeft_comp_assoc, ih]
    simp only [whiskerLeft_comp, Category.assoc, tensorHom_def]
    monoidal

variable {C} [SymmetricCategory C]

private lemma unit_adjacent (n : ℕ) (i : Fin n) :
    (adjacentIso (𝟙_ C) n i).hom = 𝟙 _ := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · change (α_ (𝟙_ C) (𝟙_ C) (power (𝟙_ C) n)).inv ≫
        ((β_ (𝟙_ C) (𝟙_ C)).hom ▷ power (𝟙_ C) n) ≫
        (α_ (𝟙_ C) (𝟙_ C) (power (𝟙_ C) n)).hom = 𝟙 _
      rw [braiding_tensorUnit_left, unitors_equal]
      simp only [Iso.hom_inv_id, id_whiskerRight, Category.id_comp, Iso.inv_hom_id]
    · change (𝟙_ C) ◁ (adjacentIso (𝟙_ C) n j).hom = 𝟙 _
      rw [ih, whiskerLeft_id]

/-- 概要：単位のテンソル冪上の全ての置換は恒等射（BF §3.1）。
方針：隣接交換が恒等射であることを対称群の生成性で全置換へ延長する。
規約：反復テンソルの括弧と単位因子を含む射全体の等式である。
使われ方：単位余代数の対称群等変性を証明する。 -/
lemma tensorUnitPower_permutation (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (permutationAction (𝟙_ C) n σ).asIso.hom = 𝟙 _ := by
  cases n with
  | zero => rfl
  | succ n =>
    have hs : σ ∈ Submonoid.closure
        (Set.range (fun i : Fin n => Equiv.swap i.castSucc i.succ)) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]
      exact Submonoid.mem_top _
    induction hs using Submonoid.closure_induction with
    | mem σ hs =>
      obtain ⟨i, rfl⟩ := hs
      change (permutationAction (𝟙_ C) (n + 1)
        (_root_.SerrePositivity.Coxeter.adjacentTransposition i)).asIso.hom = _
      rw [permutationAction_adjacent]
      exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.unit_adjacent n i
    | one => exact permutationAction_one _ _
    | mul σ τ _ _ hσ hτ =>
      rw [permutationAction_mul, hτ, hσ, Category.id_comp]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
