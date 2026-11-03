module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ConeHomotopyRepresentation
public import SerrePositivity.InfinityCategories.Derived.Gluing.Nonempty
public import SerrePositivity.DifferentialGraded.Module.ConeRotation

/-! 恒等射の標準円錐から、零加群の全 dg 自然なホモトピー表現可能性を回収する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits CochainComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
local notation "G" => DGGluingObject R C D M
local notation "K" => moduleToHomotopy R (DGGluingObject R C D M)
local notation "P" => dgRepresentableHomotopyProperty R (DGGluingObject R C D M)

/-- 任意の種対象の恒等射の円錐を使う、零加群の表現可能性。 -/
lemma dgGluingZeroHomotopyRepresentable_of_object (X : DGGluingObject R C D M)
    (hC : IsDGPretriangulated R C) (hD : IsDGPretriangulated R D) :
    dgHomotopyRepresentable R G (zeroModule R G) := by
  have hrep := dgGluingChosenConeHomotopyRepresentable R C D M X X
    (𝟙 (ForgetEnrichment.of (Complex R) X)) hC hD
  have hrep' : P ((K).obj (moduleCone R G
      (𝟙 (ForgetEnrichment.of (Complex R) (representable R X))))) := by
    simpa only [dgHomotopyRepresentable, dgModuleHomotopyProperty,
      CategoryTheory.Functor.map_id] using! hrep
  change P ((K).obj (moduleZero R G))
  exact (P).prop_of_iso
    ((moduleConeId_isZero R G (ForgetEnrichment.of (Complex R) (representable R X))).iso
      ((K).map_isZero (moduleZero_isZero R G))) hrep'

/-- 元の両圏の前三角性だけから、gluing の零加群はホモトピー表現可能。 -/
lemma dgGluingZeroHomotopyRepresentable
    (hC : IsDGPretriangulated R C) (hD : IsDGPretriangulated R D) :
    dgHomotopyRepresentable R G (zeroModule R G) := by
  obtain ⟨X⟩ := dgGluing_nonempty R C D M hC hD
  exact dgGluingZeroHomotopyRepresentable_of_object R C D M X hC hD

end SerrePositivity.InfinityCategories
