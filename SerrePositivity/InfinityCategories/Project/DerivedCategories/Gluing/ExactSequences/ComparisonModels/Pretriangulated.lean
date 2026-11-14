module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomotopyRepresentations.ShiftHomotopyRepresentation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Models.HomotopyClosurePositive
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Models.HomotopyClosureCone

/-! 双加群に沿う native dg gluing は、元の二圏が前三角的なら前三角的。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C) (hD : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D)
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M
local notation "H" => ModuleHomotopyCategory R G
local notation "K" => moduleToHomotopy R G
local notation "P" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableHomotopyProperty R G
include hC hD

/-- 表現可能加群の同型閉包は、負も含む任意整数シフトで閉じる。 -/
lemma dgGluingRepresentableProperty_shift (A : H) (hA : P A) (n : ℤ) : P (A⟦n⟧) := by
  obtain ⟨X, ⟨e⟩⟩ := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableHomotopyProperty_iff R G A).1 hA
  have hX := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingChosenShiftHomotopyRepresentable R C D M X n hC hD
  have hX' : P (((K).obj (ForgetEnrichment.of (Complex R) (representable R X)))⟦n⟧) :=
    (P).prop_of_iso (((K).commShiftIso n).app
      (ForgetEnrichment.of (Complex R) (representable R X))) hX
  exact (P).prop_of_iso ((shiftFunctor H n).mapIso e).symm hX'

lemma dgGluingRepresentable_stableUnderShift : (P).IsStableUnderShift ℤ where
  isStableUnderShiftBy n :=
    ⟨fun A hA => dgGluingRepresentableProperty_shift R C D M hC hD A hA n⟩

/-- 元の二 dg 圏の前三角性を明示入力として、実 dg gluing の前三角性を供給する。 -/
lemma dgGluing_isDGPretriangulated : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R G where
  toContainsZero := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRepresentable_containsZero R C D M hC hD
  toIsStableUnderShift := dgGluingRepresentable_stableUnderShift R C D M hC hD
  toIsTriangulatedClosed₂ := by
    let := dgGluingRepresentable_stableUnderShift R C D M hC hD
    let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRepresentable_isTriangulatedClosed₃ R C D M hC hD
    exact ObjectProperty.IsTriangulatedClosed₂.of_isTriangulatedClosed₃

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
