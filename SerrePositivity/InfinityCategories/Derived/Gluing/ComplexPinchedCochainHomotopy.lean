module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CochainCylinder
public import SerrePositivity.InfinityCategories.Derived.Gluing.TrivialFibrationHomotopy
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomotopyRetargetValue
public import SerrePositivity.InfinityCategories.Derived.ComplexPinchedQuasiIso
public import SerrePositivity.InfinityCategories.F1B.HomotopyWhiskering

/-! 全比較 cochain の境界式を、実 pinched 空間の全単体ホモトピーへ移す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory CochainComplex HomComplex DifferentialGraded
variable {R : Type u} [CommRing R]

def dgGluingComplexPinchedCylinderHomotopy (K : Complex R) :
    SSet.Homotopy (complexPinchedMap.{u, v} (dgGluingCochainCylinderZero K))
      (complexPinchedMap.{u, v} (dgGluingCochainCylinderOne K)) := by
  let : QuasiIso (dgGluingCochainCylinderProjection K) :=
    dgGluingCochainCylinderProjection_quasiIso K
  let : TrivialKanFibration (complexPinchedMap.{u, v} (dgGluingCochainCylinderProjection K)) :=
    complexPinchedMap_trivialKanFibration _ (dgGluingCochainCylinderProjection_surjective K)
  apply dgGluingHomotopy_of_trivialFibration_post_eq
    (complexPinchedMap.{u, v} (dgGluingCochainCylinderProjection K))
  rw [← complexPinchedMap_comp, ← complexPinchedMap_comp,
    dgGluingCochainCylinderZero_projection, dgGluingCochainCylinderOne_projection]

def dgGluingComplexPinchedHomotopy_of_cochain {K L : Complex R}
    (f g : K ⟶ L) (h : Cochain K L (-1)) (he : δ (-1) 0 h = Cochain.ofHom (g - f)) :
    SSet.Homotopy (complexPinchedMap.{u, v} f) (complexPinchedMap.{u, v} g) := by
  refine stableHomotopyRetarget
    (functorHomotopyPostcomp (dgGluingComplexPinchedCylinderHomotopy.{u, v} K)
      (complexPinchedMap.{u, v} (dgGluingCochainCylinderExtension f g h he))) ?_ ?_
  · rw [← complexPinchedMap_comp, dgGluingCochainCylinderExtension_zero]
  · rw [← complexPinchedMap_comp, dgGluingCochainCylinderExtension_one]

end SerrePositivity.InfinityCategories
