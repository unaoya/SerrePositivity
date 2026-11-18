module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.InsertionMoveFirst
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SchurPartialEquivariance

/-!
模型。文献の定義との比較は後で
# Schur 作用の任意の位置での部分合成公理

概要：Berger–Moerdijk §1 の自由代数の作用の部分合成則を任意の入力位置で証明する。
方針：入力位置を先頭からのブロック移動で表し、先頭の合成則と両側の置換則を合わせる。
規約：標準の comp と tensorInsertionAction を使い、arity 零も含める。
使われ方：Schur 対象を自由オペラッド代数へ拡張する。
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

/-- 概要：Schur 作用は前方 a、後方 b の任意の代入位置で合成則を満たす（Berger–Moerdijk §1）。
方針：先頭ブロック移動の対角作用を前置し、両側の等変性で先頭の代数公理へ戻す。
規約：指定位置は a、外側の入力数は a+b+1。
使われ方：一般の Fin による入力位置の合成公理へ移す。 -/
lemma schurAction_comp_at_sum (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (K : Complex A) (a b n : ℕ) :
    (P.comp (a + b) n ⟨a, by omega⟩ ▷
      power ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj K) (a + b + n)) ≫
      P.schurAction K (a + b + n) =
    (α_ (P.arity (a + b + 1)) (P.arity n)
      (power ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj K) (a + b + n))).hom ≫
      (P.arity (a + b + 1) ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj K)
        (P.arity n) (a + b) n ⟨a, by omega⟩ (P.schurAction K n)) ≫
      P.schurAction K (a + b + 1) := by
  let σ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadMoveFirstBlock a b 1
  let ω := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadMoveFirstBlock a b n
  let e := (P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation (a + b + 1) σ) ▷ P.arity n) ⊗ₘ
    (permutationAction ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj K) (a + b + n) ω).asIso.hom
  have : IsIso e := by dsimp [e]; infer_instance
  apply (cancel_epi e).1
  dsimp only [e]
  have hl := P.schurAction_comp_outer_equivariance K (a + b) n 0 σ
  dsimp only [σ] at hl
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation_moveFirst, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadMoveFirstBlock_zero] at hl
  rw [hl, P.schurAction_comp_zero]
  have hn := associator_naturality
    (P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation (a + b + 1) σ)) (𝟙 (P.arity n))
    (permutationAction ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj K) (a + b + n) ω).asIso.hom
  simp only [tensorHom_id, id_tensorHom] at hn
  erw [reassoc_of% hn, tensorHom_comp_whiskerLeft_assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction_moveFirst]
  rw [← whiskerLeft_comp_tensorHom_assoc, P.schurAction_equivariance]
  rfl

/-- 概要：Schur 作用は全ての入力位置についてオペラッド代数の部分合成公理を満たす（Berger–Moerdijk §1）。
方針：入力位置の値と後方の長さで外側の arity を分解し、区間長による合成則を適用する。
規約：外側の arity は m+1、合成後は m+n。
使われ方：自由オペラッド代数の comp_action フィールドを与える。 -/
lemma schurAction_comp (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (K : Complex A) (m n : ℕ) (i : Fin (m + 1)) :
    (P.comp m n i ▷ power ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj K) (m + n)) ≫
      P.schurAction K (m + n) =
    (α_ (P.arity (m + 1)) (P.arity n)
      (power ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj K) (m + n))).hom ≫
      (P.arity (m + 1) ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj K)
        (P.arity n) m n i (P.schurAction K n)) ≫ P.schurAction K (m + 1) := by
  rcases i with ⟨a, ha⟩
  generalize hb : m - a = b
  have hm : m = a + b := by omega
  subst m
  exact P.schurAction_comp_at_sum K a b n

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
