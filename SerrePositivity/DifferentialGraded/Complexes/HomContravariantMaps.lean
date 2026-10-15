module
public import SerrePositivity.DifferentialGraded.Complexes.HomContravariant
public import SerrePositivity.DifferentialGraded.Complexes.ClosedMaps

/-! # 反変Hom dg関手の閉零射での計算 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite CochainComplex HomComplex
variable (A : Type u) [CommRing A]

lemma homContravariantDG_closedMap {P Q : Complex A} (f : P ⟶ Q) (T : Complex A) :
    closedMap A f ≫ (homContravariantDG A T).map (op Q) (op P) =
      closedMap A (homPrecompose f T) := by
  apply (unitCycleEquiv _).injective
  apply Subtype.ext
  change (cycleFromUnit _ (closedMap A f ≫ (homContravariantDG A T).map (op Q) (op P))).val =
    (cycleFromUnit _ (closedMap A (homPrecompose f T))).val
  rw [cycleFromUnit_postcomp, closedMap_cycle, closedMap_cycle]
  apply Cochain.ext₀
  intro r
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro g
  change (((homContravariantDG A T).map (op Q) (op P)).f 0 (Cochain.ofHom f)).v
      r r (add_zero r) g = (homPrecompose f T).f r g
  rw [homContravariantDG_map_element]
  simp only [zero_mul, Int.negOnePow_zero, one_smul]
  rfl

end SerrePositivity.DifferentialGraded
