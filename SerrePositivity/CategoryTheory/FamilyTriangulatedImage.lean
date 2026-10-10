module

public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# 三角関手の族の本質像

各成分での射を同時に持ち上げられる関手の族について、
対象の族の本質像は成分ごとの完全三角形による拡大で閉じる。
積の圏に三角構造を別途構成することなく、この閉包性を利用する。
-/

@[expose] public section

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

variable {ι C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  (F : ι → C ⥤ D) [∀ i, (F i).CommShift ℤ] [∀ i, (F i).IsTriangulated]

/-- 関手の族の全成分で同時に表せる対象の族。 -/
def familyEssImage (Y : ι → D) : Prop := ∃ X : C, ∀ i, Nonempty ((F i).obj X ≅ Y i)

omit [∀ i, (F i).IsTriangulated] [∀ i, (F i).CommShift ℤ]
  [Preadditive C] [HasShift C ℤ] [Preadditive D] [HasShift D ℤ]
  [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasZeroObject D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] in
/-- 成分ごとの同型は同時の代表の存在を保つ。 -/
lemma familyEssImage_of_iso {Y Z : ι → D} (hY : familyEssImage F Y)
    (e : ∀ i, Y i ≅ Z i) : familyEssImage F Z := by
  obtain ⟨X, hX⟩ := hY
  exact ⟨X, fun i ↦ ⟨(hX i).some ≪≫ e i⟩⟩

omit [∀ i, (F i).IsTriangulated] [Preadditive C] [Preadditive D]
  [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasZeroObject D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] in
/-- 一様なシフトは同時の代表の存在を保つ。 -/
lemma familyEssImage_shift {Y : ι → D} (hY : familyEssImage F Y) (n : ℤ) :
    familyEssImage F (fun i ↦ (Y i)⟦n⟧) := by
  obtain ⟨X, hX⟩ := hY
  exact ⟨X⟦n⟧, fun i ↦ ⟨((F i).commShiftIso n).app X ≪≫
    (shiftFunctor D n).mapIso (hX i).some⟩⟩

/-- 成分ごとの射を同時に持ち上げられれば、本質像は完全三角形による拡大で閉じる。 -/
lemma familyEssImage_extension
    (hfull : ∀ (X Y : C) (f : ∀ i, (F i).obj X ⟶ (F i).obj Y),
      ∃ g : X ⟶ Y, ∀ i, (F i).map g = f i)
    (T : ι → Triangle D) (hT : ∀ i, T i ∈ distTriang D)
    (h₁ : familyEssImage F (fun i ↦ (T i).obj₁))
    (h₃ : familyEssImage F (fun i ↦ (T i).obj₃)) :
    familyEssImage F (fun i ↦ (T i).obj₂) := by
  obtain ⟨X₁, he₁⟩ := h₁
  obtain ⟨X₃, he₃⟩ := h₃
  let e₁ := fun i ↦ (he₁ i).some
  let e₃ := fun i ↦ (he₃ i).some
  obtain ⟨f, hf⟩ := hfull X₃ (X₁⟦(1 : ℤ)⟧) (fun i ↦
    (e₃ i).hom ≫ (T i).mor₃ ≫ (e₁ i).inv⟦(1 : ℤ)⟧' ≫
      ((F i).commShiftIso (1 : ℤ)).inv.app X₁)
  obtain ⟨X₂, a, b, hU⟩ := distinguished_cocone_triangle₂ f
  refine ⟨X₂, fun i ↦ ⟨Triangle.π₂.mapIso (isoTriangleOfIso₁₃ _ _
    ((F i).map_distinguished _ hU) (hT i) (e₁ i) (e₃ i) ?_)⟩⟩
  simp [hf, ← Functor.map_comp]

end SerrePositivity
