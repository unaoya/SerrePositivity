module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.AlgebraEvaluation
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.AlgebraEvaluationOne
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SchurInputNaturality
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SchurGeneratorExt
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SchurAction

/-!
模型。文献の定義との比較は後で
# 評価射の作用保存を全合成の評価へ帰着する

概要：Berger–Moerdijk §1 の自由代数からの評価射が作用を保つ条件を生成射で判定する。
方針：入力の生成射を評価する式と、Schur 作用の生成射上の式を用いる。
規約：判定条件の各内側 arity は独立に零を許す。
使われ方：任意の代数の全合成の評価から自由・忘却随伴の余単位を構成する。
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

attribute [local implicit_reducible] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：Schur 入力の生成射を評価すると各入力の代数作用をテンソルした射になる（Berger–Moerdijk §1）。
方針：有限テンソル生成射の自然性へ各 arity の評価の式を適用する。
規約：すべての入力に同じ評価射を適用する。
使われ方：評価射の作用保存を、全合成と個別の作用の比較へ帰着する。 -/
lemma schurInputGenerator_evaluation (X : P.Algebra) (n : ℕ) (s : Fin n → ℕ) :
    P.schurInputGenerator X.carrier n s ≫ _root_.SerrePositivity.TensorPowers.map X.evaluation n =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator X.carrier
        (fun r => P.arity r ⊗ power X.carrier r) X.action n s := by
  have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator_naturality
    (fun r => P.arity r ⊗ power X.carrier r)
    (fun r => P.arity r ⊗ power X.carrier r)
    (fun r => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A P.sequence X.carrier r) X.action X.evaluation
    (fun r => 𝟙 (P.arity r ⊗ power X.carrier r))
    (fun r => by simpa only [Category.id_comp] using X.ι_evaluation r) n s
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.schurInputGenerator, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap_id, Category.id_comp] using h

/-- 概要：評価射の作用保存と全合成の評価式は同値である（Berger–Moerdijk §1）。
方針：両辺を独立な内側 arity の生成射へ制限し、生成射による一意性を用いる。
規約：この同値自体は全合成の評価式の成立を仮定しない。
使われ方：全合成の評価の帰納法を随伴の余単位の作用保存へ接続する。 -/
lemma evaluation_action_iff (X : P.Algebra) (n : ℕ) :
    (P.schurAction X.carrier n ≫ X.evaluation =
      (P.arity n ◁ _root_.SerrePositivity.TensorPowers.map X.evaluation n) ≫ X.action n) ↔
    ∀ s : Fin n → ℕ,
      P.schurOperationTensor X.carrier n s ≫ X.action (∑ i, s i) =
      (P.arity n ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator X.carrier
        (fun r => P.arity r ⊗ power X.carrier r) X.action n s) ≫ X.action n := by
  have hgen (s : Fin n → ℕ) :
      (P.arity n ◁ P.schurInputGenerator X.carrier n s) ≫
          (P.schurAction X.carrier n ≫ X.evaluation) =
        (P.arity n ◁ P.schurInputGenerator X.carrier n s) ≫
          ((P.arity n ◁ _root_.SerrePositivity.TensorPowers.map X.evaluation n) ≫ X.action n) ↔
      P.schurOperationTensor X.carrier n s ≫ X.action (∑ i, s i) =
        (P.arity n ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator X.carrier
          (fun r => P.arity r ⊗ power X.carrier r) X.action n s) ≫ X.action n := by
    rw [← Category.assoc, P.schurInputGenerator_action,
      P.schurOperationGenerator_eq_tensor, Category.assoc, X.ι_evaluation]
    rw [← whiskerLeft_comp_assoc, X.schurInputGenerator_evaluation]
  constructor
  · intro h s
    apply (hgen s).mp
    rw [h]
  · intro h
    apply P.schurInputGenerator_hom_ext X.carrier n (P.arity n) X.carrier
    intro s
    exact (hgen s).mpr (h s)

/-- 概要：評価射は一入力の作用を保存する（Berger–Moerdijk §1）。
方針：生成射による判定を用い、一入力の全合成の評価式を適用する。
規約：内側の演算は零入力を含む。
使われ方：評価射の全 arity の作用保存の一次の成分を与える。 -/
lemma evaluation_action_one (X : P.Algebra) :
    P.schurAction X.carrier 1 ≫ X.evaluation =
      (P.arity 1 ◁ _root_.SerrePositivity.TensorPowers.map X.evaluation 1) ≫ X.action 1 := by
  exact (X.evaluation_action_iff 1).mpr X.schurOperationTensor_action_one

/-- 概要：空の内側演算族の全合成の評価は元の零入力の作用に一致する（Berger–Moerdijk §1）。
方針：空の有限テンソル族の定義を展開して単位子の整合性を使う。
規約：零入力の演算を除外せず、空の入力族をテンソル単位で表す。
使われ方：全合成の評価を帰納法で示す際の零入力の基底となる。 -/
lemma schurOperationTensor_action_zero (X : P.Algebra) (s : Fin 0 → ℕ) :
    P.schurOperationTensor X.carrier 0 s ≫ X.action (∑ i, s i) =
    (P.arity 0 ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator X.carrier
      (fun r => P.arity r ⊗ power X.carrier r) X.action 0 s) ≫ X.action 0 := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.schurOperationTensor, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composition, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeFirstInputs,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily,
    Fin.sum_univ_zero, eqToIso.hom, Iso.symm_hom, eqToHom_refl,
    id_whiskerRight, Category.id_comp, Category.comp_id, tensorHom_id,
    whiskerLeft_id]
  monoidal

/-- 概要：評価射は零入力の作用を保存する（Berger–Moerdijk §1）。
方針：生成射による判定へ空の全合成の評価を適用する。
規約：定数演算の保存を明示的に含める。
使われ方：評価射の全 arity の作用保存の零次の成分を与える。 -/
lemma evaluation_action_zero (X : P.Algebra) :
    P.schurAction X.carrier 0 ≫ X.evaluation =
      (P.arity 0 ◁ _root_.SerrePositivity.TensorPowers.map X.evaluation 0) ≫ X.action 0 := by
  exact (X.evaluation_action_iff 0).mpr X.schurOperationTensor_action_zero

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra
