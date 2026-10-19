module

public import SerrePositivity.EInfinity.Operad.ConvolutionEvaluationFirstBlock
public import SerrePositivity.EInfinity.Operad.ConvolutionAssemblyTransport
public import SerrePositivity.EInfinity.Operad.CoInsertionZero

/-!
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

namespace SerrePositivity.EInfinity

open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A]

attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
attribute [local implicit_reducible] TensorPowers.power
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
      tensorInsertionAction X C m n 0 θ =
    (α_ C (power X n) (power X m)).inv ≫ (θ ▷ power X m) := by
  rw [tensorInsertionAction_zero]
  simp only [whiskerLeft_comp, Category.assoc, whiskerLeft_eqToHom,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    whiskerLeft_hom_inv_assoc]

private lemma evaluation_append_swap (H B : Complex A) (n m : ℕ) :
    (((appendIso (homComplex A H B) n m).hom ≫
        eqToHom (congrArg (power (homComplex A H B)) (Nat.add_comm n m))) ⊗ₘ
      ((appendIso H n m).hom ≫ eqToHom (congrArg (power H) (Nat.add_comm n m)))) ≫
      convolutionPowerEvaluation H B (m + n) =
    (tensorμ (power (homComplex A H B) n) (power (homComplex A H B) m)
        (power H n) (power H m) ≫
      (convolutionPowerEvaluation H B n ⊗ₘ convolutionPowerEvaluation H B m)) ≫
      ((appendIso B n m).hom ≫ eqToHom (congrArg (power B) (Nat.add_comm n m))) := by
  rw [← tensorHom_comp_tensorHom, Category.assoc,
    convolutionPowerEvaluation_index H B (Nat.add_comm n m),
    ← convolutionPowerEvaluation_append_assoc]
  simp only [Category.assoc]

namespace Operad

/-- 概要：先頭への convolution の代入の評価は余代入の組み立てに一致する（BF §3.1）。
方針：入力の連結同型で前合成し、二ブロックの評価と三つの移送図式を使う。
規約：係数の対角を保ち、余代入と代入には同じ先頭位置を用いる。
使われ方：余代数・代数の部分合成公理から convolution の部分合成則を得る。 -/
lemma convolutionAction_insertion_zero_evaluation {P : Operad A}
    (hP : Hopf P) (H : P.Coalgebra) (B : P.Algebra) (m n : ℕ) :
    (tensorInsertionAction (homComplex A H.carrier B.carrier) (P.arity n) m n 0
        (convolutionAction hP H B n) ▷ power H.carrier (m + 1)) ≫
      convolutionPowerEvaluation H.carrier B.carrier (m + 1) =
    convolutionAssembly (hP.diagonal.map.app (FiniteBijection.of n))
      (tensorCoInsertionAction H.carrier (P.arity n) m n 0 (H.coaction n))
      (convolutionPowerEvaluation H.carrier B.carrier (m + n))
      (tensorInsertionAction B.carrier (P.arity n) m n 0 (B.action n)) := by
  let F := homComplex A H.carrier B.carrier
  let v := (appendIso F n m).hom ≫
    eqToHom (congrArg (power F) (Nat.add_comm n m))
  let w := (appendIso H.carrier n m).hom ≫
    eqToHom (congrArg (power H.carrier) (Nat.add_comm n m))
  let t := (appendIso B.carrier n m).hom ≫
    eqToHom (congrArg (power B.carrier) (Nat.add_comm n m))
  apply (cancel_epi ((P.arity n ◁ v) ▷ power H.carrier (m + 1))).1
  have h := convolutionAssembly_transport
    (hP.diagonal.map.app (FiniteBijection.of n))
    ((α_ (P.arity n) H.carrier (power H.carrier m)).inv ≫
      (H.coaction n ▷ power H.carrier m))
    (tensorμ (power F n) (power F m) (power H.carrier n) (power H.carrier m) ≫
      (convolutionPowerEvaluation H.carrier B.carrier n ⊗ₘ
        convolutionPowerEvaluation H.carrier B.carrier m))
    ((α_ (P.arity n) (power B.carrier n) (power B.carrier m)).inv ≫
      (B.action n ▷ power B.carrier m))
    (tensorCoInsertionAction H.carrier (P.arity n) m n 0 (H.coaction n))
    (convolutionPowerEvaluation H.carrier B.carrier (m + n))
    (tensorInsertionAction B.carrier (P.arity n) m n 0 (B.action n)) v w t
    (by rw [tensorCoInsertionAction_zero]; simp only [w, Category.assoc])
    (evaluation_append_swap H.carrier B.carrier n m)
    (tensorInsertionAction_zero_append B.carrier (P.arity n) m n (B.action n))
  apply Eq.trans ?_ h.symm
  dsimp only [v, F]
  simp only [← comp_whiskerRight_assoc]
  rw [tensorInsertionAction_zero_append]
  simp only [comp_whiskerRight, Category.assoc]
  exact convolutionAction_firstBlock_evaluation hP H B n m

end Operad

end SerrePositivity.EInfinity
