module

public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-! # ホモトピー圏の対象の性質と写像錐

## 概要

写像錐で閉じた複体の性質がホモトピー圏の対象の性質に降りること、ホモトピー圏の完全三角形の写像錐による代表、三角形を指定した充満部分圏へ制限することを与える。

## 方針

Mathlib の `HomotopyCategory` の完全三角形が写像錐の三角形と同型であることを使う。

## 規約

性質は `ObjectProperty` で書く。

## 使われ方

PerfectComplex の台付き完全複体、Asymptotic の列の複体。
-/

@[expose] public noncomputable section

universe v u

section HomotopyConeRepresentativePart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
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

end HomotopyConeRepresentativePart

section HomotopyPropertyPart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
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

end HomotopyPropertyPart

section FullSubcategoryTrianglePart

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

variable {C : Type*} [Category* C] [HasShift C ℤ]
  (P : ObjectProperty C)
  (T : Triangle C) (h₁ : P T.obj₁) (h₂ : P T.obj₂) (h₃ : P T.obj₃)

section

variable [P.IsStableUnderShift ℤ]

/-- 三頂点が部分圏に属する三角形の制限。 -/
@[implicit_reducible]
noncomputable def fullSubcategoryTriangle : Triangle P.FullSubcategory :=
  Triangle.mk (show (⟨T.obj₁, h₁⟩ : P.FullSubcategory) ⟶ ⟨T.obj₂, h₂⟩ from P.homMk T.mor₁)
    (show (⟨T.obj₂, h₂⟩ : P.FullSubcategory) ⟶ ⟨T.obj₃, h₃⟩ from P.homMk T.mor₂)
    (P.ι.preimage (X := ⟨T.obj₃, h₃⟩)
      (Y := (⟨T.obj₁, h₁⟩ : P.FullSubcategory)⟦(1 : ℤ)⟧)
      (T.mor₃ ≫ (P.ι.commShiftIso (1 : ℤ)).inv.app ⟨T.obj₁, h₁⟩))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- 制限した三角形の像は元の三角形と同型。 -/
noncomputable def fullSubcategoryTriangleIso :
    P.ι.mapTriangle.obj (fullSubcategoryTriangle P T h₁ h₂ h₃) ≅ T :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [fullSubcategoryTriangle]) (by simp [fullSubcategoryTriangle])
    (by
      dsimp only [fullSubcategoryTriangle, Functor.mapTriangle, Triangle.mk, Iso.refl]
      rw [(shiftFunctor C (1 : ℤ)).map_id, Category.comp_id, Category.id_comp]
      change P.ι.map (P.ι.preimage (X := ⟨T.obj₃, h₃⟩)
        (Y := (⟨T.obj₁, h₁⟩ : P.FullSubcategory)⟦(1 : ℤ)⟧) _) ≫ _ = T.mor₃
      rw [P.ι.map_preimage]
      simp)

end

variable [Preadditive C] [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [P.IsTriangulated]

lemma fullSubcategoryTriangle_distinguished (hT : T ∈ distTriang C) :
    fullSubcategoryTriangle P T h₁ h₂ h₃ ∈ distTriang P.FullSubcategory :=
  isomorphic_distinguished T hT _ (fullSubcategoryTriangleIso P T h₁ h₂ h₃)

end SerrePositivity

end FullSubcategoryTrianglePart
