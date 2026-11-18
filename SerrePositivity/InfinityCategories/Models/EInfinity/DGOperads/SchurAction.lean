module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SchurTensorDescent
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SchurCompositionEquivariance

/-!
模型。文献の定義との比較は後で
# Schur 対象上のオペラッドの作用射

概要：Berger–Moerdijk §1 の自由代数の作用射を、全入力への合成から構成する。
方針：Schur 演算の生成射の内側等変性を使い、独立な入力の余極限から降ろす。
規約：ここでは作用射と生成射上の式を構成する。代数の公理は別途証明する。
使われ方：自由オペラッド代数の構成で、各 arity の作用の chain map となる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A]

/-- 概要：Schur 対象上の n 入力の作用射（Berger–Moerdijk §1）。
方針：全入力への合成の生成射を、各入力の同時置換への不変性によって余極限から降ろす。
規約：arity 0 を含み、各 arity の作用は複体射である。
使われ方：自由代数の底の複体をオペラッド代数へ拡張するための作用射となる。 -/
def schurAction (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (K : Complex A) (n : ℕ) :
    P.arity n ⊗ power ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj K) n ⟶ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj K :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurTensorArityDesc P.sequence K (P.arity n) ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj K) n
    (fun s => P.schurOperationGenerator K n s)
    (fun s τ => P.schurOperationGenerator_inner_equivariance K n s τ)

/-- 概要：Schur 対象の作用射は生成射上で全入力への合成の式を取る（Berger–Moerdijk §1）。
方針：余極限の降下射の計算則を用い、始域の比較同型を相殺する。
規約：内側の arity の有限族を固定する。
使われ方：作用の代数公理と自由代数の普遍性を生成射上で検証する。 -/
@[reassoc]
lemma schurInputGenerator_action (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (K : Complex A) (n : ℕ) (s : Fin n → ℕ) :
    (P.arity n ◁ P.schurInputGenerator K n s) ≫ P.schurAction K n =
      P.schurOperationGenerator K n s := by
  apply (cancel_epi (P.arity n ◁ eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurTensorDiagram_obj_ofArity P.sequence K n s))).1
  let f := fun s => P.schurOperationGenerator K n s
  let hf := fun s τ => P.schurOperationGenerator_inner_equivariance K n s τ
  have h := P.schurInputGenerator_desc K (P.arity n) ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj K) n
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurTensorArityFamily P.sequence K (P.arity n) ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj K) n f)
    (fun σ => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurTensorArityFamily_naturality P.sequence K (P.arity n)
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj K) n f hf σ) s
  exact h.trans (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurTensorArityFamily_ofArity P.sequence K (P.arity n)
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj K) n f s)

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
