module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Insertion
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.InsertionBlockNaturality
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.InsertionPrefixNaturality

/-!
模型。文献の定義との比較は後で
# テンソル冪への代入と底の複体射の自然性

概要：Berger–Moerdijk §1 の演算を保つ複体射はテンソル冪への全位置の代入を保つ。
方針：入力を三ブロックに分け、分割・連結と三ブロックへの代入の自然性を使う。
規約：零入力の演算も含み、係数の複体は固定する。
使われ方：代数の積や一般の極限を底の複体で構成する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A]

attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
attribute [local implicit_reducible] _root_.SerrePositivity.TensorPowers.power

private lemma split_natural {X Y : Complex A} (f : X ⟶ Y) (m n : ℕ) :
    _root_.SerrePositivity.TensorPowers.map f (m + n) ≫ (appendIso Y m n).inv =
      (appendIso X m n).inv ≫ (_root_.SerrePositivity.TensorPowers.map f m ⊗ₘ _root_.SerrePositivity.TensorPowers.map f n) := by
  apply (cancel_epi (appendIso X m n).hom).1
  rw [← Category.assoc, ← appendIso_naturality]
  simp only [Category.assoc, Iso.hom_inv_id, Iso.hom_inv_id_assoc, Category.comp_id]

private lemma split_three_natural {X Y : Complex A} (f : X ⟶ Y) (s n t : ℕ) :
    _root_.SerrePositivity.TensorPowers.map f (s + (n + t)) ≫ (appendIso Y s (n + t)).inv ≫
      (power Y s ◁ (appendIso Y n t).inv) =
    (appendIso X s (n + t)).inv ≫ (power X s ◁ (appendIso X n t).inv) ≫
      (_root_.SerrePositivity.TensorPowers.map f s ⊗ₘ (_root_.SerrePositivity.TensorPowers.map f n ⊗ₘ _root_.SerrePositivity.TensorPowers.map f t)) := by
  rw [reassoc_of% (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.split_natural f s (n + t)), tensorHom_comp_whiskerLeft, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.split_natural,
    ← whiskerLeft_comp_tensorHom]

private lemma insertion_blocks (K C : Complex A) (m n : ℕ) (i : Fin (m + 1))
    (θ : C ⊗ power K n ⟶ K) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction K C m n i θ =
    (C ◁ (eqToHom (congrArg (power K) (by omega : m + n = i.val + (n + (m - i.val)))) ≫
      (appendIso K i.val (n + (m - i.val))).inv ≫
      (power K i.val ◁ (appendIso K n (m - i.val)).inv))) ≫
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionBlock C (power K i.val) (power K (m - i.val)) (power K n) K θ ≫
    (appendIso K i.val (m - i.val + 1)).hom ≫
      eqToHom (congrArg (power K) (by omega : i.val + (m - i.val + 1) = m + 1)) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionBlock, whiskerLeft_comp, Category.assoc]
  rw [← reassoc_of% (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.insertionPrefix_naturality C (power K i.val)
    (appendIso K n (m - i.val)).inv)]

/-- 概要：演算を保つ複体射は全位置のテンソル代入を保つ（BM §1）。
方針：入力の三ブロックの分割、演算の比較、出力の連結の自然性を合成する。
規約：係数 C と入力数を固定し、底の複体を任意の射 f で移す。
使われ方：射影後の代数の合成公理から積の代数公理を検証する。 -/
@[reassoc]
lemma tensorInsertionAction_base_naturality {X Y C : Complex A} (f : X ⟶ Y)
    (m n : ℕ) (i : Fin (m + 1)) (θ : C ⊗ power X n ⟶ X) (θ' : C ⊗ power Y n ⟶ Y)
    (hθ : (C ◁ _root_.SerrePositivity.TensorPowers.map f n) ≫ θ' = θ ≫ f) :
    (C ◁ _root_.SerrePositivity.TensorPowers.map f (m + n)) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction Y C m n i θ' =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction X C m n i θ ≫ _root_.SerrePositivity.TensorPowers.map f (m + 1) := by
  have hs : _root_.SerrePositivity.TensorPowers.map f (m + n) ≫
      (eqToHom (congrArg (power Y) (by omega : m + n = i.val + (n + (m - i.val)))) ≫
        (appendIso Y i.val (n + (m - i.val))).inv ≫
        (power Y i.val ◁ (appendIso Y n (m - i.val)).inv)) =
    (eqToHom (congrArg (power X) (by omega : m + n = i.val + (n + (m - i.val)))) ≫
      (appendIso X i.val (n + (m - i.val))).inv ≫
      (power X i.val ◁ (appendIso X n (m - i.val)).inv)) ≫
      (_root_.SerrePositivity.TensorPowers.map f i.val ⊗ₘ
        (_root_.SerrePositivity.TensorPowers.map f n ⊗ₘ _root_.SerrePositivity.TensorPowers.map f (m - i.val))) := by
    rw [map_index_eq_assoc f (by omega : m + n = i.val + (n + (m - i.val))),
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.split_three_natural]
    simp only [Category.assoc]
  have ho : (appendIso X i.val (m - i.val + 1)).hom ≫
      eqToHom (congrArg (power X) (by omega : i.val + (m - i.val + 1) = m + 1)) ≫
      _root_.SerrePositivity.TensorPowers.map f (m + 1) =
    (_root_.SerrePositivity.TensorPowers.map f i.val ⊗ₘ _root_.SerrePositivity.TensorPowers.map f (m - i.val + 1)) ≫
      (appendIso Y i.val (m - i.val + 1)).hom ≫
      eqToHom (congrArg (power Y) (by omega : i.val + (m - i.val + 1) = m + 1)) := by
    rw [← map_index_eq f (by omega : i.val + (m - i.val + 1) = m + 1),
      ← reassoc_of% (appendIso_naturality f i.val (m - i.val + 1))]
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.insertion_blocks, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.insertion_blocks]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [← whiskerLeft_comp_assoc, ← whiskerLeft_comp_assoc,
    ← whiskerLeft_comp_assoc]
  simp only [Category.assoc]
  rw [hs]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionBlock_naturality_assoc _ _ _ f θ θ' hθ, ho]
  rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
