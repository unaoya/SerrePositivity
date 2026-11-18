module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.HadamardData

/-!
模型。文献の定義との比較は後で
# Hadamard 積の結合則

概要：Berger–Moerdijk §1 の二種類の部分合成の結合則をテンソル積へ移す。
方針：三対を分離して各列の結合則を適用する。
規約：arity の等式による移送を明示的に保つ。
使われ方：Hadamard オペラッドを公理ごとに構成する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A]

set_option maxHeartbeats 800000 in
-- 六因子のテンソルと arity の移送の型を同時に照合するため。
/-- 概要：Hadamard 積の入れ子の結合則（Berger–Moerdijk §1）。
方針：左右の反復合成を分離射の後の各列の反復合成へ直す。
規約：結合に伴う arity の移送を二列で行う。
使われ方：Hadamard オペラッドの入れ子の結合則となる。 -/
lemma nested_assoc (P Q : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (m n k : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.comp P Q m (n + 1) i ▷ (P.arity k ⊗ Q.arity k)) ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.comp P Q (m + n) k ⟨i.val + j.val, by omega⟩ =
    (α_ (P.arity (m + 1) ⊗ Q.arity (m + 1))
      (P.arity (n + 1) ⊗ Q.arity (n + 1)) (P.arity k ⊗ Q.arity k)).hom ≫
      ((P.arity (m + 1) ⊗ Q.arity (m + 1)) ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.comp P Q n k j) ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.comp P Q m (n + k) i ≫
      (eqToHom (congrArg P.arity (Nat.add_assoc m n k).symm) ⊗ₘ
        eqToHom (congrArg Q.arity (Nat.add_assoc m n k).symm)) := by
  change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.pair (P.comp m (n + 1) i) (Q.comp m (n + 1) i) ▷ _) ≫
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.pair (P.comp (m + n) k _) (Q.comp (m + n) k _) =
    _ ≫ (_ ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.pair (P.comp n k j) (Q.comp n k j)) ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.pair (P.comp m (n + k) i) (Q.comp m (n + k) i) ≫ _
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.pair_left, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.pair_right_assoc, tensorHom_comp_tensorHom]
  exact congrArg (fun f => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.separate (P.arity (m + 1)) (Q.arity (m + 1))
    (P.arity (n + 1)) (Q.arity (n + 1)) (P.arity k) (Q.arity k) ≫ f)
      (congrArg₂ (fun f g => f ⊗ₘ g) (P.nested_assoc m n k i j)
        (Q.nested_assoc m n k i j))


set_option maxHeartbeats 800000 in
-- 六因子の交換と複数の arity の移送の型を同時に照合するため。
/-- 概要：Hadamard 積の独立な二代入の結合則（Berger–Moerdijk §1）。
方針：移送を挟んだ合成を分離し、後二対の交換を各列へ移す。
規約：空の挿入区間を許し、i<j の位置補正を保つ。
使われ方：Hadamard オペラッドの独立な代入の結合則となる。 -/
lemma parallel_assoc (P Q : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (m n k : ℕ)
    (i j : Fin (m + 2)) (hij : i.val < j.val) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.comp P Q (m + 1) n i ▷ (P.arity k ⊗ Q.arity k)) ≫
      ((eqToHom (congrArg P.arity (by omega : m + 1 + n = m + n + 1)) ⊗ₘ
        eqToHom (congrArg Q.arity (by omega : m + 1 + n = m + n + 1))) ▷
          (P.arity k ⊗ Q.arity k)) ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.comp P Q (m + n) k ⟨j.val + n - 1, by omega⟩ =
    (α_ (P.arity (m + 2) ⊗ Q.arity (m + 2))
      (P.arity n ⊗ Q.arity n) (P.arity k ⊗ Q.arity k)).hom ≫
      ((P.arity (m + 2) ⊗ Q.arity (m + 2)) ◁
        (β_ (P.arity n ⊗ Q.arity n) (P.arity k ⊗ Q.arity k)).hom) ≫
      (α_ (P.arity (m + 2) ⊗ Q.arity (m + 2))
        (P.arity k ⊗ Q.arity k) (P.arity n ⊗ Q.arity n)).inv ≫
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.comp P Q (m + 1) k j ▷ (P.arity n ⊗ Q.arity n)) ≫
      ((eqToHom (congrArg P.arity (by omega : m + 1 + k = m + k + 1)) ⊗ₘ
        eqToHom (congrArg Q.arity (by omega : m + 1 + k = m + k + 1))) ▷
          (P.arity n ⊗ Q.arity n)) ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.comp P Q (m + k) n ⟨i.val, by omega⟩ ≫
      (eqToHom (congrArg P.arity (by omega : m + k + n = m + n + k)) ⊗ₘ
        eqToHom (congrArg Q.arity (by omega : m + k + n = m + n + k))) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.comp]
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.pair_left_post, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.pair_left_post_assoc]
  erw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.separate_swap_assoc (P.arity (m + 2)) (Q.arity (m + 2))
    (P.arity n) (Q.arity n) (P.arity k) (Q.arity k)]
  simp only [tensorHom_comp_tensorHom, Category.assoc]
  exact congrArg (fun f => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.separate (P.arity (m + 2)) (Q.arity (m + 2))
    (P.arity n) (Q.arity n) (P.arity k) (Q.arity k) ≫ f)
      (congrArg₂ (fun f g => f ⊗ₘ g)
        (by simpa only [eqToHom_whiskerRight, Category.assoc] using
          P.parallel_assoc m n k i j hij)
        (by simpa only [eqToHom_whiskerRight, Category.assoc] using
          Q.parallel_assoc m n k i j hij))

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard
