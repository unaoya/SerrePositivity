module

public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-! # 三角形を指定した充満部分圏へ制限する -/

@[expose] public section

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
