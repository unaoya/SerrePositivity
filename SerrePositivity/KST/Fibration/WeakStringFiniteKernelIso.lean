module
public import SerrePositivity.KST.Fibration.FiniteProductLocalizedIso
public import SerrePositivity.KST.Fibration.KernelPostRealization

/-! # 元の Verdier 包含による全 cofiber 係数の有限積の局所化同型 -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits SSet
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 同じ核値 cofiber 係数の実写像の全有限積は、全正反復で局所化同型。 -/
theorem weakStringFiniteKernelPostMap_verdier_localized_isIso
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (n r : ℕ) :
    IsIso (AnodyneHomotopy.anodyneQ.map (Limits.Pi.map (fun _ : Fin n =>
      (multiRealizationFunctor (r + 1)).map (kernelPostExact i q)))) :=
  finProduct_map_anodyneQ_isIso _
    (kernelPostExact_verdier_multiRealization_localized_isIso h r) n

end SerrePositivity.KST.Fibration
