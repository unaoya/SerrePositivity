module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Basic
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.InsertionBaseNaturality

/-!
模型。文献の定義との比較は後で
# 射の族によるオペラッド代数公理の判定

概要：Berger–Moerdijk §1 の代数公理を、共同単射な射の族の後で判定する。
方針：テンソル冪の置換・単位・代入の自然性で既存の代数公理へ帰着する。
規約：射の族の添字は空でもよく、零入力の作用も保存する。
使われ方：底の複体の極限に代数構造を入れる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A] {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A} {J : Type v}
  (X : Complex A) (B : J → P.Algebra) (p : ∀ j, X ⟶ (B j).carrier)
  (action : ∀ n, P.arity n ⊗ power X n ⟶ X)
  (hcomm : ∀ j n, action n ≫ p j = (P.arity n ◁ _root_.SerrePositivity.TensorPowers.map (p j) n) ≫ (B j).action n)
  (hjoint : ∀ {T : Complex A} (f g : T ⟶ X), (∀ j, f ≫ p j = g ≫ p j) → f = g)

attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
attribute [local implicit_reducible] SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level

include hcomm hjoint

/-- 概要：共同単射な射の後で等変性を判定する（BM §1）。
方針：テンソル冪の置換の自然性を使う。
規約：全ての置換を含む。
使われ方：極限上の代数構造の等変性を検証する。 -/
lemma joint_equivariance (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation n σ) ⊗ₘ
      (permutationAction X n σ).asIso.hom) ≫ action n = action n := by
  apply hjoint
  intro j
  simp only [Category.assoc, hcomm]
  erw [tensorHom_comp_whiskerLeft_assoc,
    ← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPower_permutation_naturality A (p j) n σ,
    ← whiskerLeft_comp_tensorHom_assoc, (B j).equivariance]
  rfl

/-- 概要：共同単射な射の後で単位則を判定する（BM §1）。
方針：一次テンソル冪と単位子の自然性を使う。
規約：各射は単位演算も保つ。
使われ方：極限上の代数構造の単位則を検証する。 -/
lemma joint_unit :
    (P.unit ▷ power X 1) ≫ action 1 = (λ_ (power X 1)).hom ≫ (oneIso X).hom := by
  apply hjoint
  intro j
  rw [Category.assoc, hcomm, ← whisker_exchange_assoc,
    (B j).unit_action]
  rw [← Category.assoc, leftUnitor_naturality, Category.assoc, oneIso_naturality]
  simp only [Category.assoc]

/-- 概要：共同単射な射の後で全位置の合成則を判定する（BM §1）。
方針：テンソル冪への代入の自然性を使う。
規約：零入力の内側演算も許す。
使われ方：極限上の代数構造の合成則を検証する。 -/
lemma joint_composition (m n : ℕ) (i : Fin (m + 1)) :
    (P.comp m n i ▷ power X (m + n)) ≫ action (m + n) =
      (α_ (P.arity (m + 1)) (P.arity n) (power X (m + n))).hom ≫
        (P.arity (m + 1) ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction X (P.arity n) m n i (action n)) ≫
        action (m + 1) := by
  apply hjoint
  intro j
  simp only [Category.assoc, hcomm]
  rw [← whisker_exchange_assoc, (B j).comp_action]
  rw [← whiskerLeft_comp_assoc,
    ← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction_base_naturality (p j) m n i _ _ (hcomm j n).symm]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [associator_naturality_right_assoc]

/-- 概要：共同単射な射が演算を保てば底の演算は代数をなす（BM §1）。
方針：単位・等変性・全位置の合成則を射の族の後で検証する。
規約：モデル構造と射影の cofibrancy を要求しない。
使われ方：積や終対象を底の複体上に構成する。 -/
def ofJointlyMonicActions : P.Algebra where
  carrier := X
  action := action
  equivariance := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.joint_equivariance X B p action hcomm hjoint
  unit_action := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.joint_unit X B p action hcomm hjoint
  comp_action := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.joint_composition X B p action hcomm hjoint

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra
