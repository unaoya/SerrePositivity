module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.PrefixSlotInput
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.IteratedCompositionEquivariance

/-!
模型。文献の定義との比較は後で
# 再帰の最初の代入と前半の外側置換

概要：Berger–Moerdijk §1 の最後の指定入力への代入が、前半の置換と両立することを示す。
方針：部分合成の外側等変性に前半の置換の位置計算を適用し、arity の移送を前後に合成する。
規約：前半 a 入力を置換し、位置 a の内側演算と未代入入力 b 個を保つ。
使われ方：末尾以外の隣接交換に関する反復合成の外側等変性の帰納段階に用いる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.Coxeter

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeFirstInputInsertion

/-- 概要：位置 a への部分合成はそれより前の置換と両立する（Berger–Moerdijk §1）。
方針：外側等変性で挿入位置が固定されることと出力の前半の置換の同定を使う。
規約：代入する内側演算には恒等射を作用させる。
使われ方：反復代入の最初の部分合成の外側等変性を与える。 -/
lemma comp_prefix_equivariance (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (a b l : ℕ) (σ : Equiv.Perm (Fin a)) :
    (P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation (a + b + 1)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadPrefixPermutation a b 1 σ)) ▷ P.arity l) ≫
        P.comp (a + b) l ⟨a, by omega⟩ =
      P.comp (a + b) l ⟨a, by omega⟩ ≫ P.sequence.map
        (_root_.SerrePositivity.FiniteBijection.permutation (a + b + l) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadPrefixPermutation a b l σ)) := by
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadPrefixPermutation_slot, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation_prefix] using
    P.outer_equivariance (a + b) l ⟨a, by omega⟩ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadPrefixPermutation a b 1 σ)

/-- 概要：反復代入の始域の前半の置換作用は部分合成の arity への移送と両立する（Berger–Moerdijk §1）。
方針：arity の置換作用の移送と前半の置換の入力位置の同定を組み合わせる。
規約：始域の arity は a+1+b、移送後は a+b+1。
使われ方：最初の部分合成の前の arity の移送に置換作用を通す。 -/
lemma arity_prefixInputPermutation_index (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (a b : ℕ) (σ : Equiv.Perm (Fin a)) :
    P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation (a + 1 + b)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadPrefixInputPermutation a b σ)) ≫
        eqToHom (congrArg P.arity (by omega : a + 1 + b = a + b + 1)) =
      eqToHom (congrArg P.arity (by omega : a + 1 + b = a + b + 1)) ≫
        P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation (a + b + 1)
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadPrefixPermutation a b 1 σ)) := by
  have h := (P.arity_permutation_index_eq (by omega : a + 1 + b = a + b + 1)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadPrefixInputPermutation a b σ)).symm
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadPrefixInputPermutation_index] at h
  exact h

/-- 概要：代入後の前半の置換作用は前半と尾を分ける arity の移送と両立する（Berger–Moerdijk §1）。
方針：arity の置換作用の移送と出力の前半のブロック置換の同定を使う。
規約：移送後の尾の長さは b+l。
使われ方：部分合成後の出力の置換を残りの反復合成の始域へ渡す。 -/
lemma arity_prefixPermutation_index (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (a b l : ℕ) (σ : Equiv.Perm (Fin a)) :
    P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation (a + b + l)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadPrefixPermutation a b l σ)) ≫
        eqToHom (congrArg P.arity (Nat.add_assoc a b l)) =
      eqToHom (congrArg P.arity (Nat.add_assoc a b l)) ≫
        P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation (a + (b + l))
          (_root_.SerrePositivity.FiniteBijection.blockEquiv σ (Equiv.refl (Fin (b + l))))) := by
  have h := (P.arity_permutation_index_eq (Nat.add_assoc a b l)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadPrefixPermutation a b l σ)).symm
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadPrefixPermutation_index] at h
  exact h

/-- 概要：再帰の最初の代入射は前半の任意の外側置換と両立する（Berger–Moerdijk §1）。
方針：始域の移送、部分合成、終域の移送の三つの可換正方形を合成する。
規約：内側演算の arity l と元の未代入入力 b 個を尾に残す。
使われ方：任意の隣接交換に関する反復合成の外側等変性で最初の代入の正方形を与える。 -/
lemma composeFirstInputInsertion_prefix_equivariance (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (a b l : ℕ)
    (σ : Equiv.Perm (Fin a)) :
    (P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation (a + 1 + b)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadPrefixInputPermutation a b σ)) ▷ P.arity l) ≫
        P.composeFirstInputInsertion a b l =
      P.composeFirstInputInsertion a b l ≫ P.sequence.map
        (_root_.SerrePositivity.FiniteBijection.permutation (a + (b + l))
          (_root_.SerrePositivity.FiniteBijection.blockEquiv σ (Equiv.refl (Fin (b + l))))) := by
  have hleft := congrArg (· ▷ P.arity l) (P.arity_prefixInputPermutation_index a b σ)
  simp only [comp_whiskerRight] at hleft
  have h₁ := congrArg (fun f => f ≫ P.comp (a + b) l ⟨a, by omega⟩ ≫
    eqToHom (congrArg P.arity (Nat.add_assoc a b l))) hleft
  have h₂ := congrArg (fun f =>
    (eqToHom (congrArg P.arity (by omega : a + 1 + b = a + b + 1)) ▷ P.arity l) ≫ f ≫
      eqToHom (congrArg P.arity (Nat.add_assoc a b l)))
    (P.comp_prefix_equivariance a b l σ)
  have h₃ := congrArg
    (((eqToHom (congrArg P.arity (by omega : a + 1 + b = a + b + 1)) ▷ P.arity l) ≫
      P.comp (a + b) l ⟨a, by omega⟩) ≫ ·)
    (P.arity_prefixPermutation_index a b l σ)
  simp only [Category.assoc] at h₁ h₂ h₃
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeFirstInputInsertion
  simp only [Category.assoc]
  exact h₁.trans (h₂.trans h₃)

/-- 概要：再帰の最初の代入射は最後の指定入力より前の隣接交換と両立する（Berger–Moerdijk §1）。
方針：前半の任意の置換に関する等変性を隣接互換へ適用し、その持ち上げを計算する。
規約：入力族の n+2 個の指定入力の末尾は交換せず、未代入入力 k 個も固定する。
使われ方：末尾以外の隣接交換に関する反復合成の帰納段階の最初の可換正方形を与える。 -/
lemma composeFirstInputInsertion_adjacent_prefix_equivariance (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A)
    (n k l : ℕ) (i : Fin n) :
    (P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation (n + 2 + k)
        (_root_.SerrePositivity.FiniteBijection.blockEquiv (adjacentTransposition i.castSucc) (Equiv.refl (Fin k)))) ▷
        P.arity l) ≫ P.composeFirstInputInsertion (n + 1) k l =
      P.composeFirstInputInsertion (n + 1) k l ≫ P.sequence.map
        (_root_.SerrePositivity.FiniteBijection.permutation ((n + 1) + (k + l))
          (_root_.SerrePositivity.FiniteBijection.blockEquiv (adjacentTransposition i) (Equiv.refl (Fin (k + l))))) := by
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadPrefixInputPermutation, permLift_adjacent] using
    P.composeFirstInputInsertion_prefix_equivariance (n + 1) k l (adjacentTransposition i)

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
