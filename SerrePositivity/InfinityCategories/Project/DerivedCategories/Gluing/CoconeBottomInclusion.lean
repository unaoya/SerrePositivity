module
public import SerrePositivity.DifferentialGraded.Complexes.Perturbation
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone

/-! 同じ mapping cocone の標準 bottom 包含と、ホモトピー零の上成分に対する擬同型性。 -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits Pretriangulated HomologicalComplex CochainComplex DifferentialGraded
variable {R : Type u} [CommRing R] {P Q : Complex R} (d : P ⟶ Q)
local notation "Qh" => _root_.HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)

/-- 標準 cone 包含を −1 シフトした、同じ cocone の実鎖写像。 -/
def dgGluingCoconeBottomInclusion : Q⟦(-1 : ℤ)⟧ ⟶ mappingCocone d :=
  (CategoryTheory.shiftFunctor (Complex R) (-1 : ℤ)).map (mappingCone.inr d)

/-- 上成分が通常の複体ホモトピー圏で零なら、同じ bottom 包含は擬同型。 -/
lemma dgGluingCoconeBottomInclusion_quasiIso (hP : IsZero ((Qh).obj P)) :
    QuasiIso (dgGluingCoconeBottomInclusion d) := by
  let T := mappingCone.triangleh d
  have hT := _root_.HomotopyCategory.mappingCone_triangleh_distinguished d
  have hi : IsIso ((Qh).map (mappingCone.inr d)) := (T.isZero₁_iff_isIso₂ hT).1 hP
  have he := (isIso_quotient_map_iff_homotopyEquivalences (mappingCone.inr d)).1 hi
  have hq : QuasiIso (mappingCone.inr d) := by
    rw [← Classical.choose_spec he]
    exact (Classical.choose he).quasiIso_hom
  unfold dgGluingCoconeBottomInclusion
  exact (quasiIso_shift_iff (mappingCone.inr d) (-1)).2 hq

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
