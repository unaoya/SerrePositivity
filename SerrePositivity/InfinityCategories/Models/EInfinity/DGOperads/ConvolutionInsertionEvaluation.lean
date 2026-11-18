module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.ConvolutionEvaluationFirstBlock
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.ConvolutionAssemblyTransport
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CoInsertionZero

/-!
模型。文献の定義との比較は後で
# 先頭への代入と余代入の評価

概要：Berger–Fresse §3.1 の convolution の先頭への代入を余代入の図式で表す。
方針：入力を二ブロックに分け、反復評価と連結の整合性で標準表示へ戻す。
規約：空の入力ブロックも許し、入力数の移送を明示する。
使われ方：convolution の先頭位置の部分合成則を証明する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A]

attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
attribute [local implicit_reducible] _root_.SerrePositivity.TensorPowers.power
attribute [local implicit_reducible] SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level

/-- 概要：連結された二ブロックへの先頭代入は最初のブロックへの作用（BM §1）。
方針：標準の先頭代入の公式で連結・入力数の移送の逆射を相殺する。
規約：長さ n のブロックを長さ m のブロックに先行させる。
使われ方：convolution の先頭ブロック評価公式へ帰着する。 -/
@[reassoc]
lemma tensorInsertionAction_zero_append (X C : Complex A) (m n : ℕ)
    (θ : C ⊗ power X n ⟶ X) :
    (C ◁ ((appendIso X n m).hom ≫
      eqToHom (congrArg (power X) (Nat.add_comm n m)))) ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction X C m n 0 θ =
    (α_ C (power X n) (power X m)).inv ≫ (θ ▷ power X m) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction_zero]
  simp only [whiskerLeft_comp, Category.assoc, whiskerLeft_eqToHom,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    whiskerLeft_hom_inv_assoc]

private lemma evaluation_append_swap (H B : Complex A) (n m : ℕ) :
    (((appendIso (homComplex A H B) n m).hom ≫
        eqToHom (congrArg (power (homComplex A H B)) (Nat.add_comm n m))) ⊗ₘ
      ((appendIso H n m).hom ≫ eqToHom (congrArg (power H) (Nat.add_comm n m)))) ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionPowerEvaluation H B (m + n) =
    (tensorμ (power (homComplex A H B) n) (power (homComplex A H B) m)
        (power H n) (power H m) ≫
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionPowerEvaluation H B n ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionPowerEvaluation H B m)) ≫
      ((appendIso B n m).hom ≫ eqToHom (congrArg (power B) (Nat.add_comm n m))) := by
  rw [← tensorHom_comp_tensorHom, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionPowerEvaluation_index H B (Nat.add_comm n m),
    ← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionPowerEvaluation_append_assoc]
  simp only [Category.assoc]

namespace Operad

/-- 概要：先頭への convolution の代入の評価は余代入の組み立てに一致する（BF §3.1）。
方針：入力の連結同型で前合成し、二ブロックの評価と三つの移送図式を使う。
規約：係数の対角を保ち、余代入と代入には同じ先頭位置を用いる。
使われ方：余代数・代数の部分合成公理から convolution の部分合成則を得る。 -/
lemma convolutionAction_insertion_zero_evaluation {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A}
    (hP : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hopf P) (H : P.Coalgebra) (B : P.Algebra) (m n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction (homComplex A H.carrier B.carrier) (P.arity n) m n 0
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionAction hP H B n) ▷ power H.carrier (m + 1)) ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionPowerEvaluation H.carrier B.carrier (m + 1) =
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly (hP.diagonalComponent n)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorCoInsertionAction H.carrier (P.arity n) m n 0 (H.coaction n))
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionPowerEvaluation H.carrier B.carrier (m + n))
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction B.carrier (P.arity n) m n 0 (B.action n)) := by
  let F := homComplex A H.carrier B.carrier
  let v := (appendIso F n m).hom ≫
    eqToHom (congrArg (power F) (Nat.add_comm n m))
  let w := (appendIso H.carrier n m).hom ≫
    eqToHom (congrArg (power H.carrier) (Nat.add_comm n m))
  let t := (appendIso B.carrier n m).hom ≫
    eqToHom (congrArg (power B.carrier) (Nat.add_comm n m))
  apply (cancel_epi ((P.arity n ◁ v) ▷ power H.carrier (m + 1))).1
  have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly_transport
    (hP.diagonalComponent n)
    ((α_ (P.arity n) H.carrier (power H.carrier m)).inv ≫
      (H.coaction n ▷ power H.carrier m))
    (tensorμ (power F n) (power F m) (power H.carrier n) (power H.carrier m) ≫
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionPowerEvaluation H.carrier B.carrier n ⊗ₘ
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionPowerEvaluation H.carrier B.carrier m))
    ((α_ (P.arity n) (power B.carrier n) (power B.carrier m)).inv ≫
      (B.action n ▷ power B.carrier m))
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorCoInsertionAction H.carrier (P.arity n) m n 0 (H.coaction n))
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionPowerEvaluation H.carrier B.carrier (m + n))
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction B.carrier (P.arity n) m n 0 (B.action n)) v w t
    (by rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorCoInsertionAction_zero]; simp only [w, Category.assoc])
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.evaluation_append_swap H.carrier B.carrier n m)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction_zero_append B.carrier (P.arity n) m n (B.action n))
  apply Eq.trans ?_ h.symm
  dsimp only [v, F]
  simp only [← comp_whiskerRight_assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction_zero_append]
  simp only [comp_whiskerRight, Category.assoc]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionAction_firstBlock_evaluation hP H B n m

end Operad

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
