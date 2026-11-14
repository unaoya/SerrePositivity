module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.PositiveShiftRepresentation

/-! 表現可能対象の同型閉包は零と非負整数シフトで閉じる。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M
local notation "H" => ModuleHomotopyCategory R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
local notation "K" => moduleToHomotopy R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
local notation "P" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableHomotopyProperty R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
variable (hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C) (hD : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D)
include hC hD

/-- 同型閉包は K(Gluing) の零対象を含む。 -/
lemma dgGluingRepresentable_containsZero : (P).ContainsZero := by
  refine ⟨⟨(K).obj (moduleZero R G), (K).map_isZero (moduleZero_isZero R G), ?_⟩⟩
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingZeroHomotopyRepresentable R C D M hC hD

/-- 代表加群の [1] の表現可能性を、同型閉包の全対象へ移す。 -/
lemma dgGluingRepresentableProperty_shift_one (A : H) (hA : P A) : P (A⟦(1 : ℤ)⟧) := by
  obtain ⟨X, ⟨e⟩⟩ := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableHomotopyProperty_iff R G A).1 hA
  have hX := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRepresentable_shift_one R C D M X hC hD
  have hX' : P (((K).obj (ForgetEnrichment.of (Complex R) (representable R X)))⟦(1 : ℤ)⟧) :=
    (P).prop_of_iso (((K).commShiftIso (1 : ℤ)).app
      (ForgetEnrichment.of (Complex R) (representable R X))) hX
  exact (P).prop_of_iso ((shiftFunctor H (1 : ℤ)).mapIso e).symm hX'

/-- 同型閉包の [1] による閉性を、そのまま対象条件の型で供給。 -/
lemma dgGluingRepresentable_stableUnderShift_one : (P).IsStableUnderShiftBy (1 : ℤ) where
  le_shift A hA := dgGluingRepresentableProperty_shift_one R C D M hC hD A hA

/-- 正シフトの反復と標準 shift 同型により、全非負整数シフトで閉じる。 -/
lemma dgGluingRepresentableProperty_shift_nat (A : H) (hA : P A) (n : ℕ) :
    P (A⟦(n : ℤ)⟧) := by
  induction n with
  | zero => exact (P).prop_of_iso ((shiftFunctorZero H ℤ).app A).symm hA
  | succ n ih =>
      have hs := dgGluingRepresentableProperty_shift_one R C D M hC hD (A⟦(n : ℤ)⟧) ih
      exact (P).prop_of_iso
        ((shiftFunctorAdd' H (n : ℤ) 1 ((n + 1 : ℕ) : ℤ) (by omega)).symm.app A) hs

/-- 同じ代表加群の任意の非負整数シフトは、全 dg 自然にホモトピー表現可能。 -/
lemma dgGluingRepresentable_shift_nat (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomotopyRepresentable R G (shiftModule (n : ℤ) (representable R X)) := by
  have hX := dgGluingRepresentableProperty_shift_nat R C D M hC hD
    ((K).obj (ForgetEnrichment.of (Complex R) (representable R X)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableHomotopyProperty_representable R G X) n
  exact (P).prop_of_iso (((K).commShiftIso (n : ℤ)).app
    (ForgetEnrichment.of (Complex R) (representable R X))).symm hX

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
