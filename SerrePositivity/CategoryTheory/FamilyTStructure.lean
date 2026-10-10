module

public import SerrePositivity.CategoryTheory.FamilyTriangulatedImage
public import Mathlib.CategoryTheory.Triangulated.TStructure.TExact

/-!
# 完全忠実な三角関手の族による t 構造

成分ごとの切り詰め三角形の左端に同時の代表があれば、
その射を持ち上げて錐を取ることで元の圏の切り詰め三角形を得る。
-/

@[expose] public section

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

variable {ι C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  (F : ι → C ⥤ D) [∀ i, (F i).CommShift ℤ] [∀ i, (F i).IsTriangulated]
  (t : TStructure D)
  (hfull : ∀ (X Y : C) (f : ∀ i, (F i).obj X ⟶ (F i).obj Y),
    ∃ g : X ⟶ Y, ∀ i, (F i).map g = f i)
  (hfaith : ∀ {X Y : C} (f g : X ⟶ Y), (∀ i, (F i).map f = (F i).map g) → f = g)
  (hcut : ∀ X : C, ∃ T : ι → Triangle D,
    (∀ i, T i ∈ distTriang D) ∧ (∀ i, t.le 0 (T i).obj₁) ∧
    (∀ i, t.ge 1 (T i).obj₃) ∧ (∀ i, Nonempty ((T i).obj₂ ≅ (F i).obj X)) ∧
    familyEssImage F (fun i ↦ (T i).obj₁))

include hfull hcut in
/-- 成分ごとの切り詰め三角形を、元の圏の一つの三角形で表す。 -/
lemma family_exists_triangle_zero_one (X : C) :
    ∃ (L R : C), (∀ i, t.le 0 ((F i).obj L)) ∧ (∀ i, t.ge 1 ((F i).obj R)) ∧
      ∃ (f : L ⟶ X) (g : X ⟶ R) (h : R ⟶ L⟦(1 : ℤ)⟧),
        Triangle.mk f g h ∈ distTriang C := by
  obtain ⟨T, hT, hle, hge, he₂, L, he₁⟩ := hcut X
  let e₁ := fun i ↦ (he₁ i).some
  let e₂ := fun i ↦ (he₂ i).some.symm
  obtain ⟨f, hf⟩ := hfull L X (fun i ↦ (e₁ i).hom ≫ (T i).mor₁ ≫ (e₂ i).inv)
  obtain ⟨R, g, h, hU⟩ := distinguished_cocone_triangle f
  refine ⟨L, R, fun i ↦ (t.le 0).prop_of_iso (e₁ i).symm (hle i), ?_, f, g, h, hU⟩
  intro i
  let ei := isoTriangleOfIso₁₂ _ _ ((F i).map_distinguished _ hU) (hT i)
    (e₁ i) (e₂ i) (by simp [hf])
  exact (t.ge 1).prop_of_iso (Triangle.π₃.mapIso ei).symm (hge i)

/-- 完全忠実な族が検出する次数条件による t 構造。 -/
noncomputable def familyTStructure : TStructure C where
  le n X := ∀ i, t.le n ((F i).obj X)
  ge n X := ∀ i, t.ge n ((F i).obj X)
  le_isClosedUnderIsomorphisms n := ⟨fun e h i ↦ (t.le n).prop_of_iso ((F i).mapIso e) (h i)⟩
  ge_isClosedUnderIsomorphisms n := ⟨fun e h i ↦ (t.ge n).prop_of_iso ((F i).mapIso e) (h i)⟩
  le_shift n a n' h X hX i := (t.le n').prop_of_iso (((F i).commShiftIso a).app X).symm
    (t.le_shift n a n' h _ (hX i))
  ge_shift n a n' h X hX i := (t.ge n').prop_of_iso (((F i).commShiftIso a).app X).symm
    (t.ge_shift n a n' h _ (hX i))
  zero' {X Y} f hX hY := hfaith f 0 (fun i ↦ by
    rw [Functor.map_zero]
    exact t.zero' _ (hX i) (hY i))
  le_zero_le X hX i := t.le_zero_le _ (hX i)
  ge_one_le X hX i := t.ge_one_le _ (hX i)
  exists_triangle_zero_one X := by
    obtain ⟨L, R, hL, hR, f, g, h, hT⟩ := family_exists_triangle_zero_one F t hfull hcut X
    exact ⟨L, R, hL, hR, f, g, h, hT⟩

/-- 各成分の評価は、誘導した t 構造に関して t 完全。 -/
lemma familyTStructure_tExact (i : ι) :
    (F i).TExact (familyTStructure F t hfull hfaith hcut) t where
  rightTExact := .mk _ _ _ (fun _ hX ↦ ⟨hX.le i⟩)
  leftTExact := .mk _ _ _ (fun _ hX ↦ ⟨hX.ge i⟩)

end SerrePositivity
