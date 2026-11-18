module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Basic
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.InsertionMoveFirst

/-!
模型。文献の定義との比較は後で
# 先頭の部分合成による代数公理の判定

概要：Berger–Moerdijk §1 の対称オペラッド代数の部分合成則を先頭位置で判定する。
方針：外側等変性と入力ブロックの回転で任意位置を先頭へ戻す。
規約：作用の単位・等変性と先頭の合成則から全入力位置の合成則を導く。
使われ方：convolution の部分合成則を前方ブロックのない評価図式へ帰着する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A] (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (X : Complex A)
  (action : ∀ n : ℕ, P.arity n ⊗ power X n ⟶ X)
  (hequiv : ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)),
    (P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation n σ) ⊗ₘ
      (permutationAction X n σ).asIso.hom) ≫ action n = action n)

attribute [local implicit_reducible] SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

include hequiv

private lemma comp_outer_equivariance (m n : ℕ) (i : Fin (m + 1))
    (σ : Equiv.Perm (Fin (m + 1))) :
    ((P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation (m + 1) σ) ▷ P.arity n) ⊗ₘ
      (permutationAction X (m + n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation m n i σ)).asIso.hom) ≫
      (P.comp m n (σ i) ▷ power X (m + n)) ≫ action (m + n) =
    (P.comp m n i ▷ power X (m + n)) ≫ action (m + n) := by
  rw [tensorHom_comp_whiskerRight_assoc, P.outer_equivariance]
  rw [← whiskerRight_comp_tensorHom_assoc, hequiv]

variable (hfirst : ∀ (m n : ℕ),
  (P.comp m n 0 ▷ power X (m + n)) ≫ action (m + n) =
    (α_ (P.arity (m + 1)) (P.arity n) (power X (m + n))).hom ≫
      (P.arity (m + 1) ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction X (P.arity n) m n 0 (action n)) ≫
      action (m + 1))

include hfirst

private lemma comp_at_sum (a b n : ℕ) :
    (P.comp (a + b) n ⟨a, by omega⟩ ▷ power X (a + b + n)) ≫ action (a + b + n) =
    (α_ (P.arity (a + b + 1)) (P.arity n) (power X (a + b + n))).hom ≫
      (P.arity (a + b + 1) ◁
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction X (P.arity n) (a + b) n ⟨a, by omega⟩ (action n)) ≫
      action (a + b + 1) := by
  let σ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadMoveFirstBlock a b 1
  let ω := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadMoveFirstBlock a b n
  let e := (P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation (a + b + 1) σ) ▷ P.arity n) ⊗ₘ
    (permutationAction X (a + b + n) ω).asIso.hom
  have : IsIso e := by dsimp [e]; infer_instance
  apply (cancel_epi e).1
  dsimp only [e]
  have hl := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.comp_outer_equivariance P X action hequiv (a + b) n 0 σ
  dsimp only [σ] at hl
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation_moveFirst, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadMoveFirstBlock_zero] at hl
  rw [hl, hfirst]
  have hn := associator_naturality
    (P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation (a + b + 1) σ)) (𝟙 (P.arity n))
    (permutationAction X (a + b + n) ω).asIso.hom
  simp only [tensorHom_id, id_tensorHom] at hn
  erw [reassoc_of% hn, tensorHom_comp_whiskerLeft_assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction_moveFirst]
  rw [← whiskerLeft_comp_tensorHom_assoc, hequiv]
  rfl

/-- 概要：等変な作用の先頭の合成則から全入力位置の合成則が従う（BM §1）。
方針：入力位置の前後の長さで外側 arity を分解し、先頭移動の置換で比較する。
規約：arity 0 の内側演算も含む。
使われ方：convolution で先頭ブロックの評価図式だけを証明すればよくする。 -/
lemma comp_action_of_first (m n : ℕ) (i : Fin (m + 1)) :
    (P.comp m n i ▷ power X (m + n)) ≫ action (m + n) =
    (α_ (P.arity (m + 1)) (P.arity n) (power X (m + n))).hom ≫
      (P.arity (m + 1) ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction X (P.arity n) m n i (action n)) ≫
      action (m + 1) := by
  rcases i with ⟨a, ha⟩
  generalize hb : m - a = b
  have hm : m = a + b := by omega
  subst m
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.comp_at_sum P X action hequiv hfirst a b n

/-- 概要：先頭の合成則から対称 P 代数を構成する（BM §1）。
方針：単位・等変性と先頭の合成則に、全位置の合成則の判定を適用する。
規約：モデル構造や cofibrancy を要求しない。
使われ方：convolution を実際の P 代数に束ねる構成に用いる。 -/
def ofFirstComposition
    (hunit : (P.unit ▷ power X 1) ≫ action 1 = (λ_ (power X 1)).hom ≫ (oneIso X).hom) :
    P.Algebra where
  carrier := X
  action := action
  equivariance := hequiv
  unit_action := hunit
  comp_action := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.comp_action_of_first P X action hequiv hfirst

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra
