module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.IteratedCompositionEquivariance
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SchurCompositionNaturality

/-!
模型。文献の定義との比較は後で
# Schur 演算の生成射と内側の coinvariant 関係

概要：Berger–Moerdijk §1 の自由代数の演算の生成射が、各内側入力の同時置換を消すことを証明する。
方針：係数と入力の置換を分離し、全入力への合成と入力の連結の等変性で出力へ運ぶ。
規約：内側の各入力の置換は独立でよく、arity 0 の入力も含む。
使われ方：生成射上の演算を Schur 入力のテンソル冪からの射へ降ろす。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers
open scoped _root_.BigOperators

variable {A : Type u} [CommRing A]

private lemma operation_invariance {C U V W R Z Y : Complex A}
    (u : U ⟶ V ⊗ W) (f : C ⊗ V ⟶ R) (l : W ⟶ Z) (q : R ⊗ Z ⟶ Y)
    (t : U ⟶ U) (b : V ⟶ V) (c : W ⟶ W) (r : R ⟶ R) (z : Z ⟶ Z)
    (hu : t ≫ u = u ≫ (b ⊗ₘ c)) (hf : (C ◁ b) ≫ f = f ≫ r)
    (hl : c ≫ l = l ≫ z) (hq : (r ⊗ₘ z) ≫ q = q) :
    (C ◁ t) ≫ (C ◁ u) ≫ (α_ C V W).inv ≫ (f ⊗ₘ l) ≫ q =
      (C ◁ u) ≫ (α_ C V W).inv ≫ (f ⊗ₘ l) ≫ q := by
  have htu : (C ◁ t) ≫ (C ◁ u) = (C ◁ u) ≫ (C ◁ (b ⊗ₘ c)) := by
    rw [← whiskerLeft_comp, hu, whiskerLeft_comp]
  have ha : (C ◁ (b ⊗ₘ c)) ≫ (α_ C V W).inv =
      (α_ C V W).inv ≫ ((C ◁ b) ⊗ₘ c) := by
    simpa only [id_tensorHom] using associator_inv_naturality (𝟙 C) b c
  have haq := congrArg (· ≫ (f ⊗ₘ l) ≫ q) ha
  simp only [Category.assoc] at haq
  have hfq : ((C ◁ b) ⊗ₘ c) ≫ (f ⊗ₘ l) ≫ q = (f ⊗ₘ l) ≫ q := by
    rw [← Category.assoc, tensorHom_comp_tensorHom, hf, hl,
      ← tensorHom_comp_tensorHom, Category.assoc, hq]
  rw [← Category.assoc _ _ ((α_ C V W).inv ≫ (f ⊗ₘ l) ≫ q), htu]
  simp only [Category.assoc]
  rw [haq, hfq]

/-- 概要：Schur 演算の生成射は内側の各入力の同時置換で変わらない（Berger–Moerdijk §1）。
方針：分離同型の自然性、全入力への合成の内側等変性、入力連結の等変性を組み合わせる。
規約：係数と入力を同じ置換で動かす diagonal 関係である。
使われ方：自由代数の作用を独立な Schur 入力ごとの coinvariant に沿って降ろす。 -/
lemma schurOperationGenerator_inner_equivariance (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (K : Complex A)
    (n : ℕ) (s : Fin n → ℕ) (τ : ∀ i, Equiv.Perm (Fin (s i))) :
    (P.arity n ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap n (fun i =>
      P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation (s i) (τ i)) ⊗ₘ
        (permutationAction K (s i) (τ i)).asIso.hom)) ≫ P.schurOperationGenerator K n s =
      P.schurOperationGenerator K n s := by
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.operation_invariance
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso n (fun i => P.arity (s i)) (fun i => power K (s i))).hom
    (P.composition n s) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso K n s).hom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A P.sequence K (∑ i, s i))
    _ _ _ _ _
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso_naturality n
      (fun i => P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation (s i) (τ i)))
      (fun i => (permutationAction K (s i) (τ i)).asIso.hom))
    (P.composition_inner_equivariance n s τ)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso_permutation K n s τ)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι_diagonal A P.sequence K (∑ i, s i) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyPermutation n s τ))

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
