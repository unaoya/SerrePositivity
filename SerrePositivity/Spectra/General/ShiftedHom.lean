module

public import SerrePositivity.Spectra.General.TensorClosed
public import SerrePositivity.Spectra.General.Suspension
public import SerrePositivity.Spectra.SymmetricSequence.FreeInternalHomShiftEvaluation

/-! # General spectra representing internal Hom out of a free spectrum

Transport the actual Sym(K) action to the shifted levelwise internal Hom.
The existing general coefficient-module evaluation theorem supplies the
structure-map formula, including its finite-bijection block exchange.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits

namespace SerrePositivity.GeneralSymmetricSpectrum
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C] {K : C}

def shiftedHom (n : ℕ) (X : C) (E : GeneralSymmetricSpectrum C K) :
    GeneralSymmetricSpectrum C K :=
  SymmetricSequence.freeShiftModule (SymmetricSequence.tensorPowerSequence K) n X E

lemma shiftedHom_level (n q : ℕ) (X : C) (E : GeneralSymmetricSpectrum C K) :
    level (shiftedHom n X E) q = (ihom X).obj (level E (n + q)) := rfl

def internalHomShiftIso (n : ℕ) (X : C) (E : GeneralSymmetricSpectrum C K) :
    internalHom ((freeAt (K := K) n).obj X) E ≅ shiftedHom n X E :=
  MonoidalModuleInternalHom.freeHomModuleIso (SymmetricSequence.tensorPowerSequence K)
    ((SymmetricSequence.freeAt n).obj X) E ≪≫
      MonoidalModuleInternalHom.transportedIso (SymmetricSequence.tensorPowerSequence K)
        ((SymmetricSequence.freeAt n).obj X) E
        (SymmetricSequence.freeInternalHomSequenceIso n X E.X)

def shiftedHomStructureIndex (n p q : ℕ) :
    FiniteBijection.of (p + (n + q)) ⟶ FiniteBijection.of (n + (p + q)) :=
  SymmetricSequence.middleExchangeIndex (FiniteBijection.of n)
    (FiniteBijection.of p) (FiniteBijection.of q)

@[reassoc] lemma shiftedHom_structureMap_evaluation (n p q : ℕ) (X : C)
    (E : GeneralSymmetricSpectrum C K) :
    X ◁ structureMap (shiftedHom n X E) p q ≫
        (ihom.ev X).app (level E (n + (p + q))) =
      (α_ X (TensorPowers.power K p) (level (shiftedHom n X E) q)).inv ≫
        (β_ X (TensorPowers.power K p)).hom ▷ level (shiftedHom n X E) q ≫
          (α_ (TensorPowers.power K p) X (level (shiftedHom n X E) q)).hom ≫
            TensorPowers.power K p ◁ (ihom.ev X).app (level E (n + q)) ≫
              structureMap E p (n + q) ≫ E.X.map (shiftedHomStructureIndex n p q) :=
  SymmetricSequence.freeShiftModule_action_component_evaluation
    (SymmetricSequence.tensorPowerSequence K) n p q X E

/-- 値域の構造射・評価・ブロック交換から直接作る内部Homの構造射。 -/
def shiftedHomStructureFormula (n p q : ℕ) (X : C)
    (E : GeneralSymmetricSpectrum C K) :
    TensorPowers.power K p ⊗ (ihom X).obj (level E (n + q)) ⟶
      (ihom X).obj (level E (n + (p + q))) :=
  CategoryTheory.MonoidalClosed.curry
    ((α_ X (TensorPowers.power K p) ((ihom X).obj (level E (n + q)))).inv ≫
      (β_ X (TensorPowers.power K p)).hom ▷ (ihom X).obj (level E (n + q)) ≫
        (α_ (TensorPowers.power K p) X ((ihom X).obj (level E (n + q)))).hom ≫
          TensorPowers.power K p ◁ (ihom.ev X).app (level E (n + q)) ≫
            structureMap E p (n + q) ≫ E.X.map (shiftedHomStructureIndex n p q))

/-- 次数をずらした内部Homの構造射は値域の構造射から直接作った射に一致する。 -/
lemma shiftedHom_structureMap_eq_formula (n p q : ℕ) (X : C)
    (E : GeneralSymmetricSpectrum C K) :
    structureMap (shiftedHom n X E) p q = shiftedHomStructureFormula n p q X E := by
  apply CategoryTheory.MonoidalClosed.uncurry_injective
  unfold shiftedHomStructureFormula
  rw [CategoryTheory.MonoidalClosed.uncurry_curry, CategoryTheory.MonoidalClosed.uncurry_eq]
  exact shiftedHom_structureMap_evaluation n p q X E

end SerrePositivity.GeneralSymmetricSpectrum
