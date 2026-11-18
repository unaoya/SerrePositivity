module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorPowerSeparation

/-!
模型。文献の定義との比較は後で
# 反復評価の対称群等変性

概要：Berger–Fresse §3.1 の反復評価は入力関数と評価点の同時置換と可換である。
方針：テンソル冪の分離を全置換へ拡張し、通常のテンソル冪の自然性を使う。
規約：全ての交換に既存の Koszul 符号が含まれる。
使われ方：convolution の対称群等変性を証明する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A]

attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：テンソル冪の分離は全ての置換と可換（BF §3.1）。
方針：隣接交換の両立を対称群の生成性で全置換へ延長する。
規約：二列へ同じ置換を作用させる。
使われ方：反復評価の同時置換の法則を証明する。 -/
@[reassoc]
lemma tensorPowerSeparation_permutation (V W : Complex A) (n : ℕ)
    (σ : Equiv.Perm (Fin n)) :
    (permutationAction (V ⊗ W) n σ).asIso.hom ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation V W n).hom =
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation V W n).hom ≫
      ((permutationAction V n σ).asIso.hom ⊗ₘ (permutationAction W n σ).asIso.hom) := by
  cases n with
  | zero =>
    change 𝟙 _ ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation V W 0).hom =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation V W 0).hom ≫ (𝟙 _ ⊗ₘ 𝟙 _)
    simp only [tensorHom_id, id_whiskerRight, Category.id_comp, Category.comp_id]
  | succ n =>
    have hs : σ ∈ Submonoid.closure
        (Set.range (fun i : Fin n => Equiv.swap i.castSucc i.succ)) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]
      exact Submonoid.mem_top _
    induction hs using Submonoid.closure_induction with
    | mem σ hs =>
      obtain ⟨i, rfl⟩ := hs
      change (permutationAction (V ⊗ W) (n + 1)
        (_root_.SerrePositivity.Coxeter.adjacentTransposition i)).asIso.hom ≫ _ =
        _ ≫ ((permutationAction V (n + 1) (_root_.SerrePositivity.Coxeter.adjacentTransposition i)).asIso.hom ⊗ₘ
          (permutationAction W (n + 1) (_root_.SerrePositivity.Coxeter.adjacentTransposition i)).asIso.hom)
      simp only [permutationAction_adjacent]
      exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation_adjacent V W n i
    | one =>
      simp only [permutationAction_one, tensorHom_id, id_whiskerRight,
        Category.id_comp, Category.comp_id]
    | mul σ τ _ _ hσ hτ =>
      rw [permutationAction_mul, permutationAction_mul, permutationAction_mul,
        Category.assoc, hσ, ← Category.assoc, hτ]
      simp only [Category.assoc, tensorHom_comp_tensorHom]

private lemma evaluation_step {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [SymmetricCategory C] {F H V W N T B : C} (s : N ⟶ V ⊗ W)
    (e : F ⊗ H ⟶ B) (q : V ⊗ W ⟶ T) :
    ((F ⊗ H) ◁ s) ≫ tensorμ F H V W ≫ tensorμ F V H W ≫ (e ⊗ₘ q) =
      e ⊗ₘ (s ≫ q) := by
  have hδ : tensorδ F V H W = tensorμ F H V W := by
    rw [tensorδ, tensorμ, SymmetricCategory.braiding_swap_eq_inv_braiding V H]
  rw [← hδ, tensorδ_tensorμ_assoc, tensorHom_def', ← whiskerLeft_comp_assoc,
    ← tensorHom_def']

/-- 概要：反復評価は対を分離してから各対を評価した射である（BF §3.1）。
方針：分離と逆向きの tensorμ を相殺して長さで帰納する。
規約：零入力の分離と評価は互いに逆の単位子。
使われ方：反復評価の自然性と等変性をテンソル冪の関手性へ帰着する。 -/
@[reassoc]
lemma convolutionPowerEvaluation_separation (H B : Complex A) (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation (homComplex A H B) H n).hom ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionPowerEvaluation H B n = _root_.SerrePositivity.TensorPowers.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionEvaluation H B) n := by
  induction n with
  | zero => exact (λ_ (𝟙_ (Complex A))).inv_hom_id
  | succ n ih =>
    have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.evaluation_step (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation (homComplex A H B) H n).hom
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionEvaluation H B) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionPowerEvaluation H B n)
    have ht := h.trans (congrArg (fun f => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionEvaluation H B ⊗ₘ f) ih)
    simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation, Iso.trans_hom, whiskerLeftIso_hom,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionPowerEvaluation, _root_.SerrePositivity.TensorPowers.map, Category.assoc] using ht

/-- 概要：反復評価は入力と評価点の同時置換と可換（BF §3.1）。
方針：分離同型を前置して、全置換との両立とテンソル冪の自然性を使う。
規約：零入力を含む任意の対称群の元に対して成り立つ。
使われ方：convolution の係数と入力の同時置換の不変性を導く。 -/
lemma convolutionPowerEvaluation_permutation (H B : Complex A) (n : ℕ)
    (σ : Equiv.Perm (Fin n)) :
    ((permutationAction (homComplex A H B) n σ).asIso.hom ⊗ₘ
      (permutationAction H n σ).asIso.hom) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionPowerEvaluation H B n =
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionPowerEvaluation H B n ≫ (permutationAction B n σ).asIso.hom := by
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation (homComplex A H B) H n).hom).1
  rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation_permutation_assoc]
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionPowerEvaluation_separation,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionPowerEvaluation_separation_assoc]
  exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPower_permutation_naturality A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionEvaluation H B) n σ).symm

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
