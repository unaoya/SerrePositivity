module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.AlgebraEvaluationCriterion
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.IteratedOperationTensor

/-!
模型。文献の定義との比較は後で
# 未処理の末尾入力を含む反復合成の評価

概要：Berger–Moerdijk §1 の全合成の評価の帰納法を、末尾入力数を固定せずに定式化する。
方針：空の演算族での評価を計算し、末尾が空の評価式を通常の全合成の評価式へ戻す。
規約：末尾の入力は各内側演算の入力の後に置く。
使われ方：自由代数の評価射の作用保存を、演算族の長さで帰納的に証明する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers
open scoped _root_.BigOperators

variable {A : Type u} [CommRing A] {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A}

attribute [local implicit_reducible] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily _root_.SerrePositivity.TensorPowers.power
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：内側の演算族が空なら、末尾入力を含む評価は元の作用に一致する（Berger–Moerdijk §1）。
方針：空の反復合成のテンソル射と、空の作用の有限テンソルを簡約する。
規約：未処理の末尾入力数 k は任意。
使われ方：全合成の評価の一般化した帰納法の零次の基底となる。 -/
lemma iteratedOperationTensor_action_zero (X : P.Algebra) (k : ℕ) (s : Fin 0 → ℕ) :
    P.iteratedOperationTensor X.carrier 0 k s ≫ X.action ((∑ i, s i) + k) =
    (P.arity (0 + k) ◁
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator X.carrier (fun r => P.arity r ⊗ power X.carrier r)
        X.action 0 s ⊗ₘ 𝟙 (power X.carrier k)) ≫ (appendIso X.carrier 0 k).hom)) ≫
      X.action (0 + k) := by
  rw [P.iteratedOperationTensor_zero]
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator, Fin.sum_univ_zero, tensorHom_id,
    id_whiskerRight, Category.id_comp]

/-- 概要：末尾が空の反復合成の評価式と通常の全合成の評価式は同値である（Berger–Moerdijk §1）。
方針：末尾の零乗を右単位子で除き、同型の前合成を相殺する。
規約：指定した演算の長さ n と各内側 arity は任意。
使われ方：末尾を残した帰納法の結論を評価射の作用保存の判定へ適用する。 -/
lemma iteratedOperationTensor_action_tail_zero_iff (X : P.Algebra)
    (n : ℕ) (s : Fin n → ℕ) :
    (P.iteratedOperationTensor X.carrier n 0 s ≫ X.action ((∑ i, s i) + 0) =
      (P.arity (n + 0) ◁
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator X.carrier (fun r => P.arity r ⊗ power X.carrier r)
          X.action n s ⊗ₘ 𝟙 (power X.carrier 0)) ≫ (appendIso X.carrier n 0).hom)) ≫
        X.action (n + 0)) ↔
    (P.schurOperationTensor X.carrier n s ≫ X.action (∑ i, s i) =
      (P.arity n ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator X.carrier
        (fun r => P.arity r ⊗ power X.carrier r) X.action n s) ≫ X.action n) := by
  rw [P.iteratedOperationTensor_tail_zero, tensorHom_id, appendIso_zero_right]
  erw [rightUnitor_naturality]
  simp only [whiskerLeft_comp, Category.assoc]
  exact (cancel_epi (P.arity n ◁
    (ρ_ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun r => P.arity (s r) ⊗ power X.carrier (s r)))).hom))

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra
