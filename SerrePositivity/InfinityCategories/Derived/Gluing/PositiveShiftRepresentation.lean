module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ZeroObject

/-! 選んだ零対象への標準円錐を使い、代表加群のシフト [1] の表現可能性を回収する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits Pretriangulated DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
local notation "G" => DGGluingObject R C D M
local notation "K" => moduleToHomotopy R (DGGluingObject R C D M)
local notation "P" => dgRepresentableHomotopyProperty R (DGGluingObject R C D M)

/-- 標準円錐と零対象から、同じ代表加群のシフト [1] はホモトピー表現可能。 -/
lemma dgGluingRepresentable_shift_one (X : DGGluingObject R C D M)
    (hC : IsDGPretriangulated R C) (hD : IsDGPretriangulated R D) :
    dgHomotopyRepresentable R G (shiftModule 1 (representable R X)) := by
  let O := dgGluingZeroObject R C D M hC hD
  let f : ForgetEnrichment.of (Complex R) X ⟶ ForgetEnrichment.of (Complex R) O := 0
  let T := moduleHomotopyConeTriangle R G ((dgYoneda R G).onClosed.map f)
  have hc := dgGluingChosenConeHomotopyRepresentable R C D M X O f hC hD
  change P T.obj₃ at hc
  have hz : IsZero T.obj₂ := dgGluingZeroObject_isZero_homotopy R C D M hC hD
  have hT : T ∈ distTriang (ModuleHomotopyCategory R G) :=
    moduleHomotopyConeTriangle_distinguished R G ((dgYoneda R G).onClosed.map f)
  have hIso : IsIso T.mor₃ := (T.isZero₂_iff_isIso₃ hT).1 hz
  let := hIso
  change P ((K).obj ((ForgetEnrichment.of (Complex R) (representable R X))⟦(1 : ℤ)⟧))
  exact (P).prop_of_iso
    (((K).commShiftIso (1 : ℤ)).app
      (ForgetEnrichment.of (Complex R) (representable R X))).symm
    ((P).prop_of_iso (asIso T.mor₃) hc)

end SerrePositivity.InfinityCategories
