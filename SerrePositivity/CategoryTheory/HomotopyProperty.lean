module
public import SerrePositivity.CategoryTheory.HomotopyConeRepresentative
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

omit [HasZeroObject C] [HasBinaryBiproducts C] in
/-- Strict image along the homotopy quotient retains the property of its representative. -/
theorem homotopyProperty_strictMap_quotient
    (P : ObjectProperty (CochainComplex C ℤ)) (K : CochainComplex C ℤ) :
    P.strictMap (HomotopyCategory.quotient _ _) ((HomotopyCategory.quotient _ _).obj K) ↔
      P K := by
  refine ⟨?_, fun h => ⟨_, h⟩⟩
  simp only [ObjectProperty.strictMap_iff]
  rintro ⟨L, h, he⟩
  obtain rfl : L = K := congr(Quotient.as $he)
  exact h

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
    obtain ⟨f, ⟨e⟩⟩ := homotopyTriangle_exists_coneRepresentative T hT
    exact ⟨_, (hquot _).mpr (hcone f hK hL), ⟨e⟩⟩

end SerrePositivity
