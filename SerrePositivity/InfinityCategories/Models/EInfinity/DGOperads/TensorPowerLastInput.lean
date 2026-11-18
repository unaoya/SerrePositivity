module

public import SerrePositivity.CategoryTheory.Monoidal.TensorPower.Basic
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamily

/-!
模型。文献の定義との比較は後で
# 最後の一入力と末尾のテンソル冪の連結

概要：Berger–Moerdijk §1 の作用の反復評価で、最後の作用の出力と未処理の末尾を連結する。
方針：一次のブロックの単位因子を、三ブロック連結の結合則と自然性で相殺する。
規約：入力の順序を保ち、末尾入力数は零を許す。
使われ方：作用の有限テンソルの最後の分離を末尾入力付きの式へ移す。
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

attribute [local implicit_reducible] _root_.SerrePositivity.TensorPowers.power
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：最後の一入力の単位因子を補って末尾を連結すると直接の連結に一致する（Berger–Moerdijk §1）。
方針：連結の結合則を使い、一次の連結の右単位子を相殺する。
規約：出力の長さ n+(k+1) を n+1+k へ移す。
使われ方：有限作用族の最後の作用と末尾入力を一つのブロックとして扱う。 -/
lemma appendIso_lastInput (X : Complex A) (n k : ℕ) :
    ((power X n ◁ (ρ_ X).inv) ▷ power X k) ≫
      ((appendIso X n 1).hom ▷ power X k) ≫ (appendIso X (n + 1) k).hom =
    (α_ (power X n) X (power X k)).hom ≫ (appendIso X n (k + 1)).hom ≫
      eqToHom (congrArg (power X) (by omega : n + (k + 1) = n + 1 + k)) := by
  apply (cancel_mono (eqToHom (congrArg (power X) (Nat.add_assoc n 1 k)))).1
  simp only [Category.assoc]
  rw [appendIso_associativity]
  erw [associator_naturality_middle_assoc]
  rw [appendIso_one_left]
  simp only [whiskerLeft_comp, Category.assoc]
  simp only [← whiskerLeft_comp_assoc, ← comp_whiskerRight_assoc,
    Iso.inv_hom_id, id_whiskerRight, Category.id_comp]
  rw [appendIso_index_right X n (Nat.one_add k).symm]
  simp only [eqToHom_trans]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
