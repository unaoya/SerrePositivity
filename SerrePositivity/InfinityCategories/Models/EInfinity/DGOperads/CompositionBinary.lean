module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CompositionUnit
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.PartialCompositionTransport

/-!
模型。文献の定義との比較は後で
# 二つの入力への合成を部分合成で記述する

概要：Berger–Moerdijk §1 の外側等変性の基底で、二つの入力への合成を部分合成へ展開する。
方針：一つの入力へ代入して尾を残す場合を簡約し、二入力の再帰へ適用する。
規約：内側 arity は 0 を含む。arity の括弧付けの移送を明示する。
使われ方：異なる入力への部分合成の交換則を全入力への合成に適用する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded
open scoped _root_.BigOperators

variable {A : Type u} [CommRing A]

/-- 概要：一つの入力への代入と k 個の未処理の入力を部分合成で表す（Berger–Moerdijk §1）。
方針：空の残りの演算族を単位子で除き、arity の移送を末尾にまとめる。
規約：代入位置は先頭の入力とし、尾の入力の順序は保つ。
使われ方：二入力への反復合成の最後の部分合成を明示する。 -/
lemma composeFirstInputs_one_raw (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (k : ℕ) (s : Fin 1 → ℕ) :
    P.composeFirstInputs 1 k s =
      (P.arity (1 + k) ◁ (ρ_ (P.arity (s 0))).hom) ≫
        (eqToHom (congrArg P.arity (by omega : 1 + k = (0 + k) + 1)) ▷ P.arity (s 0)) ≫
          P.comp (0 + k) (s 0) 0 ≫
            eqToHom (congrArg P.arity (by simp; omega : (0 + k) + s 0 = (∑ i, s i) + k)) := by
  rw [P.composeFirstInputs_succ_factor]
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeFirstInputs, eqToHom_refl,
    Category.id_comp, Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySubstitutionStep_zero_post]
  simp only [Category.assoc, eqToHom_trans]
  rfl

/-- 概要：一つの入力へ代入して k 個を残す合成を標準の arity で表す（Berger–Moerdijk §1）。
方針：再帰の式の 0+k を部分合成の arity の移送で k に直す。
規約：代入位置は先頭とし、未処理の入力の順序は保つ。
使われ方：二入力への反復合成の後半を通常の部分合成へ簡約する。 -/
lemma composeFirstInputs_one (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (k : ℕ) (s : Fin 1 → ℕ) :
    P.composeFirstInputs 1 k s =
      (P.arity (1 + k) ◁ (ρ_ (P.arity (s 0))).hom) ≫
        (eqToHom (congrArg P.arity (by omega : 1 + k = k + 1)) ▷ P.arity (s 0)) ≫
          P.comp k (s 0) 0 ≫
            eqToHom (congrArg P.arity (by simp; omega : k + s 0 = (∑ i, s i) + k)) := by
  have hc := P.comp_index_eq (Nat.zero_add k) (Eq.refl (s 0)) 0
  simp only [eqToHom_refl, tensorHom_id, Fin.cast_zero] at hc
  have hp := congrArg
    (· ≫ eqToHom (congrArg P.arity (by simp; omega : k + s 0 = (∑ i, s i) + k))) hc
  simp only [Category.assoc, eqToHom_trans] at hp
  rw [P.composeFirstInputs_one_raw, hp.symm, ← comp_whiskerRight_assoc, eqToHom_trans]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
