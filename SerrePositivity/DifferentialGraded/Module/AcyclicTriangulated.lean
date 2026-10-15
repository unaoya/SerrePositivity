module
public import SerrePositivity.DifferentialGraded.Module.Acyclic
public import SerrePositivity.DifferentialGraded.Module.HomotopyEvaluationTriangles
public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-! # K(D)のacyclic部分圏とVerdier局所化の射のクラス -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Pretriangulated ZeroObject
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

instance moduleHomotopyAcyclicClosedUnderIso :
    (moduleHomotopyAcyclic A D).IsClosedUnderIsomorphisms where
  of_iso e h x := (_root_.HomotopyCategory.subcategoryAcyclic (ModuleCat A)).prop_of_iso
    ((moduleHomotopyEvaluation A D x).mapIso e) (h x)

instance moduleHomotopyAcyclicContainsZero : (moduleHomotopyAcyclic A D).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, fun x =>
    (_root_.HomotopyCategory.subcategoryAcyclic (ModuleCat A)).prop_of_isZero
      ((moduleHomotopyEvaluation A D x).map_isZero (isZero_zero _))⟩

instance moduleHomotopyAcyclicStableShift : (moduleHomotopyAcyclic A D).IsStableUnderShift ℤ where
  isStableUnderShiftBy s := ⟨fun M h x =>
    ((_root_.HomotopyCategory.subcategoryAcyclic (ModuleCat A)).inverseImage
      (moduleHomotopyEvaluation A D x)).le_shift s M (h x)⟩

instance moduleHomotopyAcyclicTriangulatedClosed₂ :
    (moduleHomotopyAcyclic A D).IsTriangulatedClosed₂ :=
  ObjectProperty.IsTriangulatedClosed₂.mk' (P := moduleHomotopyAcyclic A D) (by
    intro T hT h₁ h₃ x
    exact (_root_.HomotopyCategory.subcategoryAcyclic (ModuleCat A)).ext_of_isTriangulatedClosed₂
      ((moduleHomotopyEvaluation A D x).mapTriangle.obj T)
      ((moduleHomotopyEvaluation A D x).map_distinguished T hT) (h₁ x) (h₃ x))

/-- 評価先のacyclic部分圏の逆像の共通部分は三角閉。 -/
instance moduleHomotopyAcyclicIsTriangulated : (moduleHomotopyAcyclic A D).IsTriangulated where

/-- Verdier局所化の射は、既に指定したobjectwise準同型そのもの。 -/
lemma moduleHomotopyAcyclic_trW_eq :
    (moduleHomotopyAcyclic A D).trW = moduleHomotopyQuasiIso A D := by
  ext M N f
  obtain ⟨M⟩ := M
  obtain ⟨N⟩ := N
  obtain ⟨f, rfl⟩ := (moduleToHomotopy A D).map_surjective f
  exact ((moduleHomotopyAcyclic A D).trW_iff_of_distinguished
    (moduleHomotopyConeTriangle A D f) (moduleHomotopyConeTriangle_distinguished A D f)).trans
      (moduleHomotopyQuasiIso_iff_acyclic_cone A D f).symm

end SerrePositivity.DifferentialGraded
