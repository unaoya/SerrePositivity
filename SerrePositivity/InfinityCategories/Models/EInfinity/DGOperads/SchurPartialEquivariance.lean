module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SchurActionFirstInsertion
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SchurActionEquivariance

/-!
模型。文献の定義との比較は後で
# 部分合成後の Schur 作用の外側置換

概要：Berger–Moerdijk §1 の外側等変性で任意位置の部分合成後の作用を比較する。
方針：オペラッドの外側等変性を全合成後の Schur 作用の等変性へ接続する。
規約：外側の係数と合成後の入力に対応する置換を同時に作用させる。
使われ方：先頭の部分合成公理を任意の入力位置へ移す。
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

/-- 概要：外側の入力位置を置換した部分合成後の Schur 作用は対応する対角作用を相殺する（Berger–Moerdijk §1）。
方針：部分合成へ外側の係数置換を通し、合成後の係数と入力の同時置換を作用で相殺する。
規約：置換後の代入位置は σ i。
使われ方：任意の部分合成公理の左辺を先頭位置の左辺へ移す。 -/
lemma schurAction_comp_outer_equivariance (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (K : Complex A)
    (m n : ℕ) (i : Fin (m + 1)) (σ : Equiv.Perm (Fin (m + 1))) :
    ((P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation (m + 1) σ) ▷ P.arity n) ⊗ₘ
      (permutationAction ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj K) (m + n)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation m n i σ)).asIso.hom) ≫
      (P.comp m n (σ i) ▷ power ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj K) (m + n)) ≫
      P.schurAction K (m + n) =
    (P.comp m n i ▷ power ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj K) (m + n)) ≫
      P.schurAction K (m + n) := by
  rw [tensorHom_comp_whiskerRight_assoc, P.outer_equivariance]
  rw [← whiskerRight_comp_tensorHom_assoc, P.schurAction_equivariance]

/-- 概要：任意位置の部分合成後の作用を、先頭との交換によって先頭の二段の作用へ移せる（Berger–Moerdijk §1）。
方針：先頭と指定位置の交換へ外側等変性を適用し、先頭の代数公理を使う。
規約：合成後の入力の置換は operadOuterPermutation で与える。
使われ方：標準の入力代入射の置換則と合わせて任意位置の代数公理を得る。 -/
lemma schurAction_comp_swap_zero (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (K : Complex A)
    (m n : ℕ) (i : Fin (m + 1)) :
    ((P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation (m + 1) (Equiv.swap 0 i)) ▷ P.arity n) ⊗ₘ
      (permutationAction ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj K) (m + n)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation m n 0 (Equiv.swap 0 i))).asIso.hom) ≫
      (P.comp m n i ▷ power ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj K) (m + n)) ≫
      P.schurAction K (m + n) =
    (α_ (P.arity (m + 1)) (P.arity n)
      (power ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj K) (m + n))).hom ≫
      (P.arity (m + 1) ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj K)
        (P.arity n) m n 0 (P.schurAction K n)) ≫ P.schurAction K (m + 1) := by
  have h := P.schurAction_comp_outer_equivariance K m n 0 (Equiv.swap 0 i)
  simpa only [Equiv.swap_apply_left, P.schurAction_comp_zero] using h

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
