module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomotopyRepresentations.ConeHomotopyRepresentation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.Nonempty
public import SerrePositivity.DifferentialGraded.Module.ConeRotation

/-! 恒等射の標準円錐から、零加群の全 dg 自然なホモトピー表現可能性を回収する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits CochainComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M
local notation "K" => moduleToHomotopy R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
local notation "P" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableHomotopyProperty R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)

/-- 任意の種対象の恒等射の円錐を使う、零加群の表現可能性。 -/
lemma dgGluingZeroHomotopyRepresentable_of_object (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
    (hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C) (hD : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomotopyRepresentable R G (zeroModule R G) := by
  have hrep := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingChosenConeHomotopyRepresentable R C D M X X
    (𝟙 (ForgetEnrichment.of (Complex R) X)) hC hD
  have hrep' : P ((K).obj (moduleCone R G
      (𝟙 (ForgetEnrichment.of (Complex R) (representable R X))))) := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomotopyRepresentable, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomotopyProperty,
      CategoryTheory.Functor.map_id] using! hrep
  change P ((K).obj (moduleZero R G))
  exact (P).prop_of_iso
    ((moduleConeId_isZero R G (ForgetEnrichment.of (Complex R) (representable R X))).iso
      ((K).map_isZero (moduleZero_isZero R G))) hrep'

/-- 元の両圏の前三角性だけから、gluing の零加群はホモトピー表現可能。 -/
lemma dgGluingZeroHomotopyRepresentable
    (hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C) (hD : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomotopyRepresentable R G (zeroModule R G) := by
  obtain ⟨X⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluing_nonempty R C D M hC hD
  exact dgGluingZeroHomotopyRepresentable_of_object R C D M X hC hD

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
