module

public import SerrePositivity.Spectra.General.ShiftedHomSuspension
public import SerrePositivity.CategoryTheory.Monoidal.Braided

/-! # The adjoint bonding map of a shifted Hom as a mapped original bonding map

The other two factors are actual isomorphisms: closed-Hom exchange and the
finite-bijection block exchange at the output. This formula is independent
of any model structure or Omega-spectrum hypothesis.
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

lemma shiftedHom_adjointStructureMap_formula (n q : ℕ) (X : C)
    (E : GeneralSymmetricSpectrum C K) :
    adjointStructureMap (shiftedHom n X E) q =
      ((ihom X).map (adjointStructureMap E (n + q)) ≫
        (InternalHomExchange.iso X K (level E ((n + q) + 1))).hom) ≫
          (ihom K).map ((ihom X).map (E.X.map (shiftedHomSuspensionIndex n q))) := by
  apply MonoidalClosed.uncurry_injective
  apply MonoidalClosed.uncurry_injective
  rw [adjointStructureMap, MonoidalClosed.uncurry_curry, MonoidalClosed.uncurry_eq]
  change X ◁ suspensionMap (shiftedHom n X E) q ≫
    (ihom.ev X).app (level E (n + (q + 1))) = _
  rw [shiftedHom_suspensionMap_evaluation]
  rw [MonoidalClosed.uncurry_natural_right, MonoidalClosed.uncurry_natural_right,
    InternalHomExchange.doubleUncurry_map_exchange, adjointStructureMap,
    MonoidalClosed.uncurry_curry]
  simp only [Category.assoc]
  rfl

end SerrePositivity.GeneralSymmetricSpectrum
