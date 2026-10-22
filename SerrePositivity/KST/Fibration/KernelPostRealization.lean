module
public import SerrePositivity.KST.Fibration.KernelPostcomposition
public import SerrePositivity.KST.Fibration.VerdierKernelRealization

/-! # 元の Verdier 包含による核への後合成は全正有限反復実現で同値 -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 元の核の cofiber 係数を運ぶ射は、全正有限反復で局所化同型。 -/
theorem kernelPostExact_verdier_multiRealization_localized_isIso
    {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
    (h : IsVerdierSequence i q) (r : ℕ) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      ((multiRealizationFunctor (r + 1)).map (kernelPostExact i q))) := by
  have := verdierKernelExact_multiRealization_localized_isIso h r
  rw [kernelPostExact_verdier_factor h, Functor.map_comp, Functor.map_comp]
  infer_instance

end SerrePositivity.KST.Fibration
