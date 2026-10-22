module
public import SerrePositivity.InfinityCategories.Derived.Gluing.KernelShiftRepresentatives
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaPostHomotopyCriterion

/-! 同じ実シフト代表射は、任意試験対象からの全 Hom にホモトピー同値を誘導する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory HomologicalComplex CochainComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (X : DGGluingObject R C D M) (n : ℤ)
  (p : DGGluingShiftRepresentative R C X.left n)
  (q : DGGluingShiftRepresentative R D X.right n)
local notation "F" => Morita.kernelTensor R D C M
local notation "S" => dgGluingKernelShiftObject R C D M X n
local notation "T" => dgGluingKernelObject R C D M
  (dgGluingShiftObjectFromRepresentatives R C D M X n p q)
local notation "a" => dgGluingKernelShiftRepresentativeMap R C D M X n p q
local notation "Qh" => _root_.HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)
variable (V : DGFunctorCommaObject R (RightModule R D) (RightModule R C)
  (Morita.kernelTensor R D C M))

/-- 同じ閉シフト代表射による、全 Hom の実後合成。 -/
def dgGluingKernelShiftRepresentativePost :
    dgFunctorCommaHomComplex R (RightModule R D) (RightModule R C) F V S ⟶
      dgFunctorCommaHomComplex R (RightModule R D) (RightModule R C) F V T :=
  eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) V)
    (Y := ForgetEnrichment.of (Complex R) S) (Y' := ForgetEnrichment.of (Complex R) T) a

/-- 両成分の代表同型により、同じ実後合成は通常複体のホモトピー圏で同型。 -/
lemma dgGluingKernelShiftRepresentativePost_isIso :
    IsIso ((Qh).map (dgGluingKernelShiftRepresentativePost R C D M X n p q V)) := by
  have hs : IsIso ((moduleToHomotopy R D).map
      ((dgFunctorCommaSource R (RightModule R D) (RightModule R C) F).onClosed.map a)) := by
    rw [dgGluingKernelShiftRepresentativeMap_source_homotopy R C D M X n p q]
    infer_instance
  have ht : IsIso ((moduleToHomotopy R C).map
      ((dgFunctorCommaReplacement R (RightModule R D) (RightModule R C) F).onClosed.map a)) := by
    rw [dgGluingKernelShiftRepresentativeMap_replacement_homotopy R C D M X n p q]
    infer_instance
  exact dgGluingCommaPostHomotopy_isIso R (RightModule R D) (RightModule R C)
    F V S T a hs ht

/-- 同じ順射自身が、実鎖写像のホモトピー同値になる。 -/
lemma dgGluingKernelShiftRepresentativePost_equivalence :
    homotopyEquivalences (ModuleCat R) (ComplexShape.up ℤ)
      (dgGluingKernelShiftRepresentativePost R C D M X n p q V) :=
  (isIso_quotient_map_iff_homotopyEquivalences _).1
    (dgGluingKernelShiftRepresentativePost_isIso R C D M X n p q V)

/-- 同じ実後合成を順射に保つ、全 Hom のホモトピー同値。 -/
def dgGluingKernelShiftRepresentativePostEquiv :
    HomotopyEquiv
      (dgFunctorCommaHomComplex R (RightModule R D) (RightModule R C) F V S)
      (dgFunctorCommaHomComplex R (RightModule R D) (RightModule R C) F V T) :=
  Classical.choose (dgGluingKernelShiftRepresentativePost_equivalence R C D M X n p q V)

lemma dgGluingKernelShiftRepresentativePostEquiv_hom :
    (dgGluingKernelShiftRepresentativePostEquiv R C D M X n p q V).hom =
      dgGluingKernelShiftRepresentativePost R C D M X n p q V :=
  Classical.choose_spec (dgGluingKernelShiftRepresentativePost_equivalence R C D M X n p q V)

end SerrePositivity.InfinityCategories
