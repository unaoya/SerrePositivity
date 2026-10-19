module

public import SerrePositivity.EInfinity.Operad.ConvolutionOperations
public import SerrePositivity.EInfinity.Operad.ConvolutionUnitCoherence

/-!
# Convolution の単位則

概要：Berger–Fresse §3.1 の Hom(H,B) の convolution 演算の単位公理を証明する。
方針：右 tensor 評価後に、Hopf 対角・余代数・代数の三つの単位則を順に使う。
規約：任意の Hopf dg オペラッド、余代数、代数に適用する。
使われ方：convolution を P 代数へ束ねる際の単位条件となる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.Operad

open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A] {P : Operad A}

attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：評価後の convolution の単位は通常の評価となる（BF §3.1）。
方針：対角の単位保存を四因子の自然性で分離し、各側の単位則を適用する。
規約：一次冪の入力を比較同型で元の内部 Hom へ移す。
使われ方：転置後の convolution の単位公理を導く。 -/
lemma convolutionUncurriedAction_unit (hP : Hopf P) (H : P.Coalgebra) (B : P.Algebra) :
    ((P.unit ▷ power (homComplex A H.carrier B.carrier) 1) ▷ H.carrier) ≫
      convolutionUncurriedAction hP H B 1 =
    ((λ_ (power (homComplex A H.carrier B.carrier) 1)).hom ▷ H.carrier) ≫
      ((oneIso (homComplex A H.carrier B.carrier)).hom ▷ H.carrier) ≫
      convolutionEvaluation H.carrier B.carrier := by
  have hd : P.unit ≫ hP.diagonal.map.app (FiniteBijection.of 1) =
      (λ_ (𝟙_ (Complex A))).inv ≫ (P.unit ⊗ₘ P.unit) := hP.diagonal.unit
  exact convolutionUnitLaw P.unit (hP.diagonal.map.app (FiniteBijection.of 1))
    (oneIso (homComplex A H.carrier B.carrier)) (oneIso H.carrier) (oneIso B.carrier)
    (H.coaction 1) (B.action 1) (convolutionPowerEvaluation H.carrier B.carrier 1)
    (convolutionEvaluation H.carrier B.carrier) hd H.unit_coaction B.unit_action
    (convolutionPowerEvaluation_one H.carrier B.carrier)

/-- 概要：convolution 演算は P 代数の単位則を満たす（BF §3.1）。
方針：単位を前合成した右転置を評価後の単位公式で比較する。
規約：係数環や余代数・代数の cofibrancy に追加条件を課さない。
使われ方：内部 Hom 上の P 代数構造の単位公理となる。 -/
lemma convolutionAction_unit (hP : Hopf P) (H : P.Coalgebra) (B : P.Algebra) :
    (P.unit ▷ power (homComplex A H.carrier B.carrier) 1) ≫
      convolutionAction hP H B 1 =
    (λ_ (power (homComplex A H.carrier B.carrier) 1)).hom ≫
      (oneIso (homComplex A H.carrier B.carrier)).hom := by
  rw [convolutionAction, ← curryRight_naturality_source]
  rw [tensorHom_id]
  rw [convolutionUncurriedAction_unit, ← comp_whiskerRight_assoc]
  rw [← convolutionEvaluation_uncurry, curryRight_uncurryRight]

end SerrePositivity.EInfinity.Operad
