module
public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-! # Mapping-cone closure descends to a homotopy-category object property -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe v u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- A property represented on complexes inherits closure under distinguished triangles
from closure under mapping cones. Its zero and shift conditions remain separate. -/
theorem homotopyProperty_isTriangulatedClosed₃
    (P : ObjectProperty (CochainComplex C ℤ))
    (Q : ObjectProperty (HomotopyCategory C (.up ℤ)))
    (hquot : ∀ K, Q ((HomotopyCategory.quotient _ _).obj K) ↔ P K)
    (hcone : ∀ {K L} (f : K ⟶ L), P K → P L → P (CochainComplex.mappingCone f)) :
    Q.IsTriangulatedClosed₃ where
  ext₃' T hT h₁ h₂ := by
    have hK : P T.obj₁.as := (hquot _).mp h₁
    have hL : P T.obj₂.as := (hquot _).mp h₂
    obtain ⟨f : T.obj₁.as ⟶ T.obj₂.as, hf⟩ :=
      (HomotopyCategory.quotient _ _).map_surjective T.mor₁
    refine ⟨_, ?_, ⟨Triangle.π₃.mapIso (isoTriangleOfIso₁₂ T _ hT
      (HomotopyCategory.mappingCone_triangleh_distinguished f)
      (Iso.refl _) (Iso.refl _) ?_)⟩⟩
    · exact (hquot _).mpr (hcone f hK hL)
    · simp [hf]

end SerrePositivity
