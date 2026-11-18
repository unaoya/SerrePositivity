module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SchurAction
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SchurInputNaturality
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SchurGeneratorExt

/-!
模型。文献の定義との比較は後で
# Schur 対象上の作用射の自然性

概要：Berger–Moerdijk §1 の自由代数の作用射が底の複体射に関して自然であることを示す。
方針：独立な入力の生成射上へ帰着し、生成射と全入力への合成の自然性を用いる。
規約：オペラッドと外側 arity を固定する。
使われ方：代数公理を証明した後、Schur 関手を自由代数関手に拡張する。
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

/-- 概要：Schur 関手の射は全 arity の作用射を保つ（Berger–Moerdijk §1）。
方針：Schur 入力の生成射で制限し、生成射上の作用の式と生成射の自然性を適用する。
規約：代数公理の証明には依存しない、構成済みの作用射の自然性である。
使われ方：自由代数関手の射の作用保存則を与える。 -/
lemma schurAction_naturality (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) {K L : Complex A} (f : K ⟶ L) (n : ℕ) :
    P.schurAction K n ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).map f =
      (P.arity n ◁ _root_.SerrePositivity.TensorPowers.map ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).map f) n) ≫ P.schurAction L n := by
  apply P.schurInputGenerator_hom_ext K n (P.arity n) ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj L)
  intro s
  rw [← Category.assoc, P.schurInputGenerator_action]
  rw [← whiskerLeft_comp_assoc, P.schurInputGenerator_naturality]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [P.schurInputGenerator_action]
  exact (P.schurOperationGenerator_naturality f n s).symm

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
