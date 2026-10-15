module
public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated

/-! # Mapping-cone representatives for distinguished homotopy triangles -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe v u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- The third vertex of a distinguished homotopy triangle is represented by a cone
on a map between its first two chosen complex representatives. -/
lemma homotopyTriangle_exists_coneRepresentative
    (T : Triangle (HomotopyCategory C (.up ℤ))) (hT : T ∈ distTriang _) :
    ∃ f : T.obj₁.as ⟶ T.obj₂.as,
      Nonempty (T.obj₃ ≅ (HomotopyCategory.quotient C (.up ℤ)).obj
        (CochainComplex.mappingCone f)) := by
  obtain ⟨f, hf⟩ := (HomotopyCategory.quotient _ _).map_surjective T.mor₁
  refine ⟨f, ⟨Triangle.π₃.mapIso (isoTriangleOfIso₁₂ T _ hT
    (HomotopyCategory.mappingCone_triangleh_distinguished f)
    (Iso.refl _) (Iso.refl _) ?_)⟩⟩
  simp [hf]

end SerrePositivity
