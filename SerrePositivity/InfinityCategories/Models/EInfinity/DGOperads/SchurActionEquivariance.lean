module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SchurOuterEquivariance
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SchurGeneratorExt
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.DiagonalEquivariance

/-!
模型。文献の定義との比較は後で
# Schur 作用の対称群に関する等変性

概要：Berger–Moerdijk §1 の自由代数の作用に対称群の関係が成立することを証明する。
方針：隣接交換の等式を生成射上で示し、対称群のモノイドとしての生成性を使う。
規約：arity 0 を含め、既存の Koszul 置換作用を用いる。
使われ方：Schur 対象上の自由オペラッド代数の等変性公理となる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers _root_.SerrePositivity.Coxeter

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：Schur 作用は外側の隣接交換の対角作用を消す（Berger–Moerdijk §1）。
方針：入力の生成射で制限し、生成射の交換の自然性と演算の外側等変性を使う。
規約：係数と Schur 入力のテンソル冪を同じ隣接交換で動かす。
使われ方：任意の対称群の元に対する作用の等変性を証明する。 -/
lemma schurAction_adjacent_equivariance (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (K : Complex A)
    (n : ℕ) (i : Fin n) :
    (P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation (n + 1) (adjacentTransposition i)) ⊗ₘ
      (adjacentIso ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj K) n i).hom) ≫
        P.schurAction K (n + 1) = P.schurAction K (n + 1) := by
  apply P.schurInputGenerator_hom_ext K (n + 1) (P.arity (n + 1))
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj K)
  intro s
  rw [← Category.assoc, whiskerLeft_comp_tensorHom,
    ← P.schurInputGenerator_adjacent K n s i, ← tensorHom_comp_whiskerLeft]
  simp only [Category.assoc]
  rw [P.schurInputGenerator_action K (n + 1) s]
  conv_lhs =>
    arg 2
    erw [P.schurInputGenerator_action K (n + 1) (fun j => s (adjacentTransposition i j))]
  exact P.schurOperationGenerator_adjacent_equivariance K n s i

/-- 概要：Schur 作用は任意の外側の置換の対角作用を消す（Berger–Moerdijk §1）。
方針：arity 0 は恒等置換だけであることを使い、正の arity は隣接交換の生成性で証明する。
規約：対称列の左作用とテンソル冪の Koszul 置換作用を同時に適用する。
使われ方：自由オペラッド代数の対称群に関する公理を与える。 -/
lemma schurAction_equivariance (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (K : Complex A) (n : ℕ)
    (σ : Equiv.Perm (Fin n)) :
    (P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation n σ) ⊗ₘ
      (permutationAction ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj K) n σ).asIso.hom) ≫
        P.schurAction K n = P.schurAction K n := by
  cases n with
  | zero =>
    have hσ : σ = 1 := Subsingleton.elim _ _
    subst σ
    simp only [_root_.SerrePositivity.FiniteBijection.permutation_one, P.sequence.map_id, permutationAction_one,
      tensorHom_id, id_whiskerRight, Category.id_comp]
  | succ n =>
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorDiagonal_equivariance_of_adjacent P.sequence
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj K) ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj K) n
      (P.schurAction K (n + 1)) (fun i => P.schurAction_adjacent_equivariance K n i) σ

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
