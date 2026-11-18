module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SchurFirstSlotAction
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SchurActionArityTransport
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.InsertionZero

/-!
模型。文献の定義との比較は後で
# 標準のテンソル代入射による Schur 作用の先頭での代数公理

概要：Berger–Moerdijk §1 の先頭での部分合成則を既存の comp と tensorInsertionAction で表す。
方針：一般の入力上の先頭の結合則へ係数と入力の arity の移送を適用する。
規約：外側の入力数を m+1、合成後の入力数を m+n とする。
使われ方：任意位置への拡張を経て自由代数の部分合成公理となる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：先頭の部分合成後の作用を補助の arity の表記へ移す（Berger–Moerdijk §1）。
方針：係数の移送を部分合成へ通し、作用の同時移送の計算則を使う。
規約：先頭の係数は 1+m、入力は n+m の表記へ移す。
使われ方：先頭の代数公理の左辺を既存の結合則の左辺へ比較する。 -/
private lemma firstInsertion_left (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (K : Complex A) (m n : ℕ) :
    ((eqToHom (congrArg P.arity (Nat.one_add m)) ▷ P.arity n) ⊗ₘ
      eqToHom (congrArg (power ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj K)) (Nat.add_comm n m))) ≫
      (P.comp m n 0 ▷ power ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj K) (m + n)) ≫
      P.schurAction K (m + n) =
    (P.composeAheadOfInputs m 0 n ▷ power ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj K) (n + m)) ≫
      P.schurAction K (n + m) := by
  rw [tensorHom_comp_whiskerRight_assoc]
  rw [← P.schurAction_index_eq K (Nat.add_comm m n)]
  rw [tensorHom_comp_tensorHom_assoc]
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeAheadOfInputs
  simp only [Nat.add_zero, eqToHom_trans, eqToHom_refl, tensorHom_id,
    comp_whiskerRight, Category.assoc]

/-- 概要：標準の先頭の入力作用を補助入力射の表記へ移す（Berger–Moerdijk §1）。
方針：係数と入力の移送を結合子へ通し、先頭代入射の比較と作用の同時移送を使う。
規約：外側の入力数を m+1 から 1+m へ移す。
使われ方：先頭の代数公理の右辺を既存の結合則の右辺へ比較する。 -/
private lemma firstInsertion_right (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (K : Complex A) (m n : ℕ) :
    ((eqToHom (congrArg P.arity (Nat.one_add m)) ▷ P.arity n) ⊗ₘ
      eqToHom (congrArg (power ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj K)) (Nat.add_comm n m))) ≫
      (α_ (P.arity (m + 1)) (P.arity n)
        (power ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj K) (m + n))).hom ≫
      (P.arity (m + 1) ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj K)
        (P.arity n) m n 0 (P.schurAction K n)) ≫ P.schurAction K (m + 1) =
    (α_ (P.arity (1 + m)) (P.arity n)
      (power ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj K) (n + m))).hom ≫
      (P.arity (1 + m) ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstSlotPowerAction ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj K)
        (P.arity n) n m (P.schurAction K n)) ≫ P.schurAction K (1 + m) := by
  have hn := associator_naturality (eqToHom (congrArg P.arity (Nat.one_add m))) (𝟙 (P.arity n))
    (eqToHom (congrArg (power ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj K)) (Nat.add_comm n m)))
  simp only [tensorHom_id, id_tensorHom] at hn
  rw [reassoc_of% hn, tensorHom_comp_whiskerLeft_assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction_zero_eq_firstSlot]
  simp only [← whiskerLeft_comp_assoc, eqToHom_trans, eqToHom_refl,
    whiskerLeft_id, Category.id_comp]
  rw [← whiskerLeft_comp_tensorHom_assoc]
  rw [P.schurAction_index_eq K (Nat.one_add m)]

/-- 概要：Schur 作用は既存の先頭への部分合成に関する代数公理を満たす（Berger–Moerdijk §1）。
方針：係数と入力の同型を前置して比較し、一般の入力上の先頭結合則へ移す。
規約：部分合成は comp m n 0、入力射は tensorInsertionAction の零位置。
使われ方：対称性で任意の入力位置へ拡張し、自由オペラッド代数を構成する。 -/
lemma schurAction_comp_zero (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (K : Complex A) (m n : ℕ) :
    (P.comp m n 0 ▷ power ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj K) (m + n)) ≫
      P.schurAction K (m + n) =
    (α_ (P.arity (m + 1)) (P.arity n)
      (power ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj K) (m + n))).hom ≫
      (P.arity (m + 1) ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj K)
        (P.arity n) m n 0 (P.schurAction K n)) ≫ P.schurAction K (m + 1) := by
  apply (cancel_epi ((eqToHom (congrArg P.arity (Nat.one_add m)) ▷ P.arity n) ⊗ₘ
    eqToHom (congrArg (power ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj K)) (Nat.add_comm n m)))).1
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.firstInsertion_left, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.firstInsertion_right]
  exact P.schurAction_firstSlot K m n

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
