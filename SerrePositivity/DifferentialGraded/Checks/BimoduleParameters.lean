module
public import SerrePositivity.DifferentialGraded.Tensor.Bimodule.Actions
public import Mathlib.Data.ZMod.Basic

/-! # 任意パラメータの全次数評価と相対tensor作用の受入監査 -/
@[expose] public section
noncomputable section
universe u v w z
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

-- Cのsmall性もKの有界性も閉次数零条件も要求しない。
example {K : Complex A} {M N : Bimodule A B C}
    (τ : BimoduleParamTrans A B C K M N) (b : B) :
    GradedNatTrans ((Center.ofBraided (Complex A)).obj K) (M.leftAt b) (N.leftAt b) :=
  Bimodule.paramLeftAt A B C τ b

example {K : Complex A} {M N : Bimodule A B C}
    {τ υ : BimoduleParamTrans A B C K M N}
    (h : ∀ b c, Bimodule.paramValue A B C τ b c = Bimodule.paramValue A B C υ b c) :
    τ = υ := Bimodule.paramValue_ext A B C h

variable [Small.{u} C] (E : Type z) [DGCategory A E]
example {K : Complex A} {P P' : Bimodule A B C} (Q : Bimodule A C E)
    (τ : BimoduleParamTrans A B C K P P') (b : B) (e : E) :
    K ⊗ (compose A B C E P Q).value b e ⟶ (compose A B C E P' Q).value b e :=
  firstParamValue A B C E Q τ b e

example {K : Complex A} (P : Bimodule A B C) {Q Q' : Bimodule A C E}
    (τ : BimoduleParamTrans A C E K Q Q') (b : B) (e : E) :
    K ⊗ (compose A B C E P Q).value b e ⟶ (compose A B C E P Q').value b e :=
  secondParamValue A B C E P τ b e

example : ((-1 : ℤ) * 1).negOnePow = (-1 : ℤˣ) := by decide

example {K : Complex A} {P P' : Bimodule A B C} (Q : Bimodule A C E)
    (τ : BimoduleParamTrans A B C K P P') (b : B) (c : C) (e : E)
    (t : K.X (-1)) (q : (Q.value c e).X 1) (v : (P.value b c).X 0) :
    (firstParamValue A B C E Q τ b e).f 0
      (ιTensorObj K ((compose A B C E P Q).value b e) (-1) (1 + 0) 0 rfl
        (t ⊗ₜ[A] BalancedTensor.element A C (Q.rightAt e) (P.leftAt b) c q v rfl)) =
    ((-1 : ℤ) * 1).negOnePow • BalancedTensor.element A C (Q.rightAt e) (P'.leftAt b) c q
      ((((Bimodule.paramValue A B C τ b c).f (-1) t).v 0 (-1) rfl) v) rfl :=
  firstParamValue_element A B C E Q τ b c e t q v rfl

example {K : Complex (ZMod 2)}
    {P P' : Bimodule (ZMod 2) PUnit.{1} PUnit.{1}}
    (Q : Bimodule (ZMod 2) PUnit.{1} PUnit.{1})
    (τ : BimoduleParamTrans (ZMod 2) PUnit.{1} PUnit.{1} K P P') :
    K ⟶ homComplex (ZMod 2)
      ((compose (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} P Q).value PUnit.unit PUnit.unit)
      ((compose (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} P' Q).value PUnit.unit PUnit.unit) :=
  firstParamHom (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} Q τ PUnit.unit PUnit.unit

#print axioms SerrePositivity.DifferentialGraded.Bimodule.paramValue
#print axioms SerrePositivity.DifferentialGraded.Bimodule.paramRightAt
#print axioms SerrePositivity.DifferentialGraded.Bimodule.paramRightAt_app
#print axioms SerrePositivity.DifferentialGraded.Bimodule.paramValue_right_naturality
#print axioms SerrePositivity.DifferentialGraded.Bimodule.paramValue_left_naturality
#print axioms SerrePositivity.DifferentialGraded.Bimodule.paramLeftAt
#print axioms SerrePositivity.DifferentialGraded.Bimodule.paramLeftAt_app
#print axioms SerrePositivity.DifferentialGraded.Bimodule.paramValue_ext
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.firstParamValue
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.secondParamValue
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.firstParamValue_element
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.secondParamValue_element
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.firstParamHom
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.secondParamHom
