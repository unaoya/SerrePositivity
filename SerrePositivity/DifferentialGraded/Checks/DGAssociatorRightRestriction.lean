module
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorRightRestriction
public import Mathlib.Data.ZMod.Basic

/-! # 外側右制限と通常結合子の可換square・非有界次数の検査 -/
@[expose] public section
noncomputable section
universe v w z t s
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor

-- 標数2、次数−2・3・−1。終端Tのsmallnessやflatnessは仮定しない。
theorem SerrePositivity.DifferentialGraded.Checks.associatorRightRestriction_charTwo_negativeDegrees
    (B : Type v) [DGCategory (ZMod 2) B] [Small.{0} B]
    (D : Type w) [DGCategory (ZMod 2) D] [Small.{0} D]
    (C : Type z) [DGCategory (ZMod 2) C] [Small.{0} C]
    (E : Type t) [DGCategory (ZMod 2) E] [Small.{0} E]
    (T : Type s) [DGCategory (ZMod 2) T] (F : DGFunctor (ZMod 2) D B)
    (P : BimoduleCategory (ZMod 2) B C) (Q : BimoduleCategory (ZMod 2) C E)
    (R : BimoduleCategory (ZMod 2) E T) (d : D) (c : C) (e : E) (t : T)
    (τ : ((BimoduleCategory.underlying (ZMod 2) E T R).value e t).X (-2))
    (q : ((BimoduleCategory.underlying (ZMod 2) C E Q).value c e).X 3)
    (p : ((BimoduleCategory.underlying (ZMod 2) B C P).value (F.obj d) c).X (-1)) :
    (composeRightRestrictionValueIso (ZMod 2) B D C T F
      (BimoduleCategory.underlying (ZMod 2) B C P)
      (BimoduleTensor.compose (ZMod 2) C E T (BimoduleCategory.underlying (ZMod 2) C E Q)
        (BimoduleCategory.underlying (ZMod 2) E T R)) d t).hom.f 0
        (associatorRightElement (ZMod 2) D C E T
          (Bimodule.rightRestriction (ZMod 2) B D C F
            (BimoduleCategory.underlying (ZMod 2) B C P))
          (BimoduleCategory.underlying (ZMod 2) C E Q)
          (BimoduleCategory.underlying (ZMod 2) E T R)
          d c e t τ q p (show (-2 : ℤ) + 3 = 1 by decide) (by decide)) =
    associatorRightElement (ZMod 2) B C E T
      (BimoduleCategory.underlying (ZMod 2) B C P)
      (BimoduleCategory.underlying (ZMod 2) C E Q)
      (BimoduleCategory.underlying (ZMod 2) E T R)
      (F.obj d) c e t τ q p (show (-2 : ℤ) + 3 = 1 by decide) (by decide) :=
  composeRightRestriction_rightElement (ZMod 2) B D C E T F P Q R d c e t τ q p
    (show (-2 : ℤ) + 3 = 1 by decide) (by decide)

#check associatorIso_rightRestriction
#print axioms composeRightRestriction_rightElement
#print axioms composeValueMap_rightRestriction_leftElement
#print axioms composeRightRestriction_leftElement
#print axioms associatorRightRestriction_left_path_element
#print axioms associatorRightRestriction_right_path_element
#print axioms associatorValue_rightRestriction
#print axioms associatorIso_rightRestriction
#print axioms
  SerrePositivity.DifferentialGraded.Checks.associatorRightRestriction_charTwo_negativeDegrees

#print axioms composeRightRestrictionValueComponent
#print axioms composeRightRestrictionValueComponent_eq
#print axioms composeRightRestrictionValueHom
#print axioms composeRightRestrictionValueHom_apply
#print axioms composeRightRestrictionValueHom_eq
#print axioms composeRightRestrictionValueComponent_element
#print axioms associatorRightRestriction_left_component_element
#print axioms associatorRightRestriction_right_component_element
#print axioms associatorValueHom_rightRestriction
