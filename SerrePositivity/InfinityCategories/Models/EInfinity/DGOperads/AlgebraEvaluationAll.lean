module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.AlgebraIteratedEvaluation
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.IteratedOperationRecursion
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.AlgebraLastInputEvaluation
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyGeneratorTailSplitLast

/-!
模型。文献の定義との比較は後で
# 任意の代数での全入力のオペラッド合成の評価

概要：Berger–Moerdijk §1 の代数の部分合成則から、任意個の演算の全合成の評価式を証明する。
方針：末尾入力を任意に残した形で演算族の長さについて帰納し、最後の部分合成則を用いる。
規約：演算族の長さ、各演算の arity、末尾入力数はいずれも零を許す。
使われ方：自由代数からの評価射と持ち上げ射の作用保存を証明する。
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
  SerrePositivity.SymmetricSequence SerrePositivity.SymmetricSequence.level
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.iteratedOperationTensor _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorLastPairExtraction
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeFirstInputInsertion appendIso _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast

/-- 概要：末尾を残した反復合成の評価は各内側演算を個別に作用させた後の外側作用に一致する（Berger–Moerdijk §1）。
方針：最後の係数と入力を取り出して帰納仮定を適用し、部分合成の評価と対称性の相殺を使う。
規約：末尾の入力は内側演算の全入力の後に置く。
使われ方：末尾入力数を零にして、自由代数の評価射の全 arity の作用保存を得る。 -/
lemma iteratedOperationTensor_action (X : P.Algebra) (n k : ℕ) (s : Fin n → ℕ) :
    P.iteratedOperationTensor X.carrier n k s ≫ X.action ((∑ i, s i) + k) =
    (P.arity (n + k) ◁
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator X.carrier (fun r => P.arity r ⊗ power X.carrier r)
        X.action n s ⊗ₘ 𝟙 (power X.carrier k)) ≫ (appendIso X.carrier n k).hom)) ≫
      X.action (n + k) := by
  induction n generalizing k with
  | zero => exact X.iteratedOperationTensor_action_zero k s
  | succ n ih =>
    let R := P.arity (n + 1 + k)
    let l := s (Fin.last n)
    apply (cancel_epi (R ◁ ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast n
      (fun j => P.arity (s j) ⊗ power X.carrier (s j))).inv ▷ power X.carrier k))).1
    rw [← Category.assoc, P.iteratedOperationTensor_succ]
    simp only [Category.assoc]
    conv_lhs =>
      arg 2
      arg 2
      arg 2
      erw [X.action_index_eq (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.oneSlotComposeOutput_eq n k s)]
    conv_lhs =>
      arg 2
      arg 2
      rw [ih (k + s (Fin.last n)) (fun j => s j.castSucc)]
    have hm := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorLastPairExtraction_map_prefix
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator X.carrier (fun r => P.arity r ⊗ power X.carrier r)
        X.action n (fun j => s j.castSucc))
      (P.composeFirstInputInsertion n k l)
      ((appendIso X.carrier l k).hom ≫
        eqToHom (congrArg (power X.carrier) (Nat.add_comm l k)))
      (appendIso X.carrier n (k + l)).hom
    have hm' := congrArg (fun z => z ≫ X.action (n + (k + l))) hm
    simp only [Category.assoc] at hm'
    refine hm'.trans ?_
    conv_lhs =>
      arg 2
      arg 2
      erw [X.composeFirstInputInsertion_action_on_blocks n k l]
    have hr := congrArg (fun z => z ≫
      (R ◁ ((appendIso X.carrier n (k + 1)).hom ≫
        eqToHom (congrArg (power X.carrier)
          (by omega : n + (k + 1) = n + 1 + k)))) ≫ X.action (n + 1 + k))
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorLastPairExtraction_reinsert R (power X.carrier n) (P.arity l)
        (power X.carrier l) (power X.carrier k) X.carrier (X.action l))
    simp only [Category.assoc, ← whiskerLeft_comp_assoc] at hr
    simp only [← whiskerLeft_comp_assoc]
    conv_lhs =>
      arg 2
      erw [hr]
    dsimp only [R]
    simp only [← whiskerLeft_comp_assoc]
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGeneratorTail_splitLast_inv X.carrier
      (fun r => P.arity r ⊗ power X.carrier r) X.action n k s]
    simp only [tensorHom_def, Category.assoc]
    rw [associator_naturality_left_assoc]

/-- 概要：全入力のオペラッド合成の評価は内側と外側の作用の合成に一致する（Berger–Moerdijk §1）。
方針：末尾入力を残した評価式へ末尾長さ零の比較を適用する。
規約：全ての零入力の内側演算を含める。
使われ方：Schur 評価射が任意の arity の作用を保つことを導く。 -/
lemma schurOperationTensor_action (X : P.Algebra) (n : ℕ) (s : Fin n → ℕ) :
    P.schurOperationTensor X.carrier n s ≫ X.action (∑ i, s i) =
      (P.arity n ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator X.carrier
        (fun r => P.arity r ⊗ power X.carrier r) X.action n s) ≫ X.action n := by
  exact (X.iteratedOperationTensor_action_tail_zero_iff n s).mp
    (X.iteratedOperationTensor_action n 0 s)

/-- 概要：Schur 評価射は全ての arity の作用を保存する（Berger–Moerdijk §1）。
方針：生成射による判定へ全入力の合成の評価式を適用する。
規約：自由代数からの評価の底の複体射についての等式。
使われ方：自由・忘却随伴の余単位を代数射として構成する。 -/
lemma evaluation_action (X : P.Algebra) (n : ℕ) :
    P.schurAction X.carrier n ≫ X.evaluation =
      (P.arity n ◁ _root_.SerrePositivity.TensorPowers.map X.evaluation n) ≫ X.action n := by
  exact (X.evaluation_action_iff n).mpr (X.schurOperationTensor_action n)

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra
