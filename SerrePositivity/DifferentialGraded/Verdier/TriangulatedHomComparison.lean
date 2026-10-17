module
public import SerrePositivity.DifferentialGraded.Verdier.ShiftedHomComparison
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-! # 三角関手の Hom 全単射性を持つ終域の三角閉性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u₁ u₂ v₁ v₂
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Pretriangulated Preadditive
open scoped ZeroObject
variable {C : Type u₁} [Category.{v₁} C] {T : Type u₂} [Category.{v₂} T]
  [HasZeroObject C] [HasZeroObject T] [Preadditive C] [Preadditive T]
  [HasShift C ℤ] [HasShift T ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor T n).Additive]
  [Pretriangulated C] [Pretriangulated T]
  (F : C ⥤ T) [F.CommShift ℤ] [F.IsTriangulated] [F.Additive]

/-- 三角形の両端への Hom が保存されれば、中間対象への Hom も保存される。 -/
lemma homComparisonTarget_triangle_obj₂ (t : Triangle C) (ht : t ∈ distTriang C)
    (h₁ : homComparisonTarget F t.obj₁) (h₃ : homComparisonTarget F t.obj₃) :
    homComparisonTarget F t.obj₂ := by
  intro X
  have h₁s := (homComparisonTarget F).le_shift (1 : ℤ) _ h₁
  have h₃s := (homComparisonTarget F).le_shift (-1 : ℤ) _ h₃
  have hker : ∀ f : X ⟶ t.obj₂, F.map f = 0 → f = 0 := by
    intro f hf
    have hz : f ≫ t.mor₂ = 0 := (h₃ X).1 (by
      rw [Functor.map_comp, hf, zero_comp, Functor.map_zero])
    obtain ⟨a, ha⟩ := Triangle.coyoneda_exact₂ t ht f hz
    have haz : F.map a ≫ (F.mapTriangle.obj t.invRotate).mor₂ = 0 := by
      change F.map a ≫ F.map t.mor₁ = 0
      rw [← Functor.map_comp, ← ha, hf]
    obtain ⟨b, hb⟩ := Triangle.coyoneda_exact₂ (F.mapTriangle.obj t.invRotate)
      (F.map_distinguished _ (inv_rot_of_distTriang _ ht)) (F.map a) haz
    obtain ⟨c, hc⟩ := (h₃s X).2 b
    have hac : a = c ≫ t.invRotate.mor₁ := (h₁ X).1 (by
      rw [Functor.map_comp, hc]
      exact hb)
    rw [ha, hac, Category.assoc]
    have hi : t.invRotate.mor₁ ≫ t.mor₁ = 0 :=
      comp_distTriang_mor_zero₁₂ _ (inv_rot_of_distTriang _ ht)
    rw [hi, comp_zero]
  constructor
  · intro f g hfg
    have hz : F.map (f - g) = 0 := by rw [Functor.map_sub, hfg, sub_self]
    exact sub_eq_zero.mp (hker (f - g) hz)
  · intro f
    obtain ⟨c, hc⟩ := (h₃ X).2 (f ≫ F.map t.mor₂)
    have hz : c ≫ t.mor₃ = 0 := (h₁s X).1 (by
      rw [Functor.map_comp, hc, Category.assoc, ← Functor.map_comp,
        comp_distTriang_mor_zero₂₃ _ ht, Functor.map_zero, comp_zero]
      exact (F.map_zero _ _).symm)
    obtain ⟨d, hd⟩ := Triangle.coyoneda_exact₃ t ht c hz
    have hdiff : (f - F.map d) ≫ (F.mapTriangle.obj t).mor₂ = 0 := by
      change (f - F.map d) ≫ F.map t.mor₂ = 0
      rw [sub_comp, ← Functor.map_comp, ← hd, hc, sub_self]
    obtain ⟨b, hb⟩ := Triangle.coyoneda_exact₂ (F.mapTriangle.obj t)
      (F.map_distinguished _ ht) (f - F.map d) hdiff
    obtain ⟨a, ha⟩ := (h₁ X).2 b
    refine ⟨d + a ≫ t.mor₁, ?_⟩
    rw [Functor.map_add, Functor.map_comp, ha]
    have hb' : f - F.map d = b ≫ F.map t.mor₁ := hb
    rw [← hb']
    abel

instance homComparisonTargetTriangulatedClosed₂ :
    (homComparisonTarget F).IsTriangulatedClosed₂ :=
  ObjectProperty.IsTriangulatedClosed₂.mk' (homComparisonTarget_triangle_obj₂ F)

instance homComparisonTargetContainsZero : (homComparisonTarget F).ContainsZero :=
  ⟨⟨0, isZero_zero C, fun X => by
    constructor
    · intro f g _
      exact (isZero_zero C).eq_of_tgt f g
    · intro f
      exact ⟨0, (F.map_isZero (isZero_zero C)).eq_of_tgt _ _⟩⟩⟩

instance homComparisonTargetIsTriangulated : (homComparisonTarget F).IsTriangulated where

end SerrePositivity.DifferentialGraded
