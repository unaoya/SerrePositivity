module
public import SerrePositivity.CategoryTheory.HomotopyProperty

public import Mathlib.Algebra.Homology.HomotopyCategory.Plus
public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated

/-!
# 共通の有限次数範囲をもつホモトピー圏

加法圏の複体について、項が有限な次数範囲の外で零となる条件を用いる。
列の加法圏へ適用すると、この範囲は列の全項に共通となる。
条件をホモトピー圏に移し、シフトと錐への安定性から三角部分圏を構成する。
代表複体自体に課す条件なので、同型閉包とは区別する。
-/

@[expose] public section

universe v u

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

variable (C : Type u) [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- ある有限な次数範囲の外で項が零となる複体の条件。 -/
def strictlyBoundedComplex : ObjectProperty (CochainComplex C ℤ) :=
  fun K ↦ ∃ a b : ℤ, K.IsStrictlyGE a ∧ K.IsStrictlyLE b

omit [HasZeroObject C] [HasBinaryBiproducts C] in
/-- Integer shifts translate a strict finite degree range. -/
lemma strictlyBoundedComplex_shift {K : CochainComplex C ℤ}
    (hK : strictlyBoundedComplex C K) (n : ℤ) : strictlyBoundedComplex C (K⟦n⟧) := by
  obtain ⟨a, b, ha, hb⟩ := hK
  exact ⟨a - n, b - n, K.isStrictlyGE_shift a n _ (by omega),
    K.isStrictlyLE_shift b n _ (by omega)⟩

/-- 有界な代表複体をもつホモトピー圏の対象の条件。 -/
def boundedHomotopyProperty : ObjectProperty (HomotopyCategory C (.up ℤ)) :=
  (strictlyBoundedComplex C).strictMap (HomotopyCategory.quotient _ _)

omit [HasZeroObject C] [HasBinaryBiproducts C] in
/-- 商関手の像における有界性は、元の複体の厳密な有界性である。 -/
@[simp] lemma boundedHomotopyProperty_quotient (K : CochainComplex C ℤ) :
    boundedHomotopyProperty C ((HomotopyCategory.quotient _ _).obj K) ↔
      strictlyBoundedComplex C K :=
  homotopyProperty_strictMap_quotient (strictlyBoundedComplex C) K

instance : (boundedHomotopyProperty C).ContainsZero where
  exists_zero :=
    ⟨(HomotopyCategory.quotient _ _).obj 0,
      Functor.map_isZero _ (isZero_zero _), by
        rw [boundedHomotopyProperty_quotient]
        exact ⟨0, 0, inferInstance, inferInstance⟩⟩

instance : (boundedHomotopyProperty C).IsStableUnderShift ℤ where
  isStableUnderShiftBy n :=
    { le_shift K hK := by
        obtain ⟨K : CochainComplex _ _, rfl⟩ := K.quotient_obj_surjective
        rw [boundedHomotopyProperty_quotient] at hK
        rw [ObjectProperty.prop_shift_iff, HomotopyCategory.shift_quotient_obj,
          boundedHomotopyProperty_quotient]
        exact strictlyBoundedComplex_shift C hK n }

omit [HasZeroObject C] in
/-- 二つの有界複体の射の錐も、明示的な共通次数範囲をもつ。 -/
lemma strictlyBoundedComplex_mappingCone {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (hK : strictlyBoundedComplex C K) (hL : strictlyBoundedComplex C L) :
    strictlyBoundedComplex C (CochainComplex.mappingCone f) := by
  obtain ⟨a, b, ha, hb⟩ := hK
  obtain ⟨c, d, hc, hd⟩ := hL
  refine ⟨min (a - 1) c, max b d, ?_, ?_⟩
  · exact CochainComplex.isStrictlyGE_mappingCone f a c _ (by omega) (by omega)
  · rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    simp only [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨K.isZero_of_isStrictlyLE b _ (by omega),
      L.isZero_of_isStrictlyLE d _ (by omega)⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance : (boundedHomotopyProperty C).IsTriangulatedClosed₃ :=
  homotopyProperty_isTriangulatedClosed₃ _ _ (boundedHomotopyProperty_quotient C)
    (fun f => strictlyBoundedComplex_mappingCone C f)

instance : (boundedHomotopyProperty C).IsTriangulated where
  toIsTriangulatedClosed₂ := .of_isTriangulatedClosed₃

/-- 共通の有限次数範囲をもつ複体のホモトピー圏。 -/
abbrev BoundedHomotopy := (boundedHomotopyProperty C).FullSubcategory

/-- 有界ホモトピー圏から全ホモトピー圏への完全忠実な三角関手。 -/
abbrev boundedHomotopyInclusion : BoundedHomotopy C ⥤ HomotopyCategory C (.up ℤ) :=
  (boundedHomotopyProperty C).ι

variable {C} {D : Type*} [Category* D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] (F : C ⥤ D) [F.Additive]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- 加法関手は共通有界な複体のホモトピー圏の関手を誘導する。 -/
@[implicit_reducible]
def mapBoundedHomotopy : BoundedHomotopy C ⥤ BoundedHomotopy D :=
  (boundedHomotopyProperty D).lift
    (boundedHomotopyInclusion C ⋙ F.mapHomotopyCategory (.up ℤ)) (by
      rintro ⟨X, hX⟩
      obtain ⟨K, rfl⟩ := X.quotient_obj_surjective
      dsimp
      simp only [boundedHomotopyProperty_quotient, strictlyBoundedComplex] at hX ⊢
      obtain ⟨a, b, ha, hb⟩ := hX
      exact ⟨a, b,
        inferInstanceAs (CochainComplex.IsStrictlyGE
          ((F.mapHomologicalComplex (.up ℤ)).obj K) a),
        inferInstanceAs (CochainComplex.IsStrictlyLE
          ((F.mapHomologicalComplex (.up ℤ)).obj K) b)⟩)

noncomputable instance : (mapBoundedHomotopy F).CommShift ℤ :=
  inferInstanceAs (((boundedHomotopyProperty D).lift
    (boundedHomotopyInclusion C ⋙ F.mapHomotopyCategory (.up ℤ)) _).CommShift ℤ)

instance : (mapBoundedHomotopy F).IsTriangulated := by
  dsimp only [mapBoundedHomotopy]
  infer_instance

end SerrePositivity
