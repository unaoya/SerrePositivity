module
public import SerrePositivity.DifferentialGraded.Perfect.CompactShift
public import SerrePositivity.DifferentialGraded.Derived.CoproductProjection
public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-! # compact dg導来対象の三角閉性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Preadditive Pretriangulated
open scoped ZeroObject
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleCompactRange_ι {J : Type u} {X : DerivedModuleCategory A D}
    (F : J → DerivedModuleCategory A D) (j : J) (f : X ⟶ F j) :
    f ≫ Sigma.ι F j ∈ (moduleCompactComparison A D X F).range := by
  classical
  exact ⟨DirectSum.lof A J (fun j => X ⟶ F j) j f,
    moduleCompactComparison_lof A D X F j f⟩

lemma moduleCompactRange_precompose {J : Type u} {X Y : DerivedModuleCategory A D}
    (hY : moduleCompact A D Y) (F : J → DerivedModuleCategory A D)
    (f : X ⟶ Y) (g : Y ⟶ ∐ F) :
    f ≫ g ∈ (moduleCompactComparison A D X F).range := by
  obtain ⟨t, a, ha⟩ := hY J F g
  rw [← ha, comp_sum]
  apply Submodule.sum_mem
  intro j _
  simpa only [Category.assoc] using moduleCompactRange_ι A D F j (f ≫ a j)

lemma moduleCompactRange_finiteProjection {J : Type u} {X : DerivedModuleCategory A D}
    (F : J → DerivedModuleCategory A D) (t : Finset J) (f : X ⟶ ∐ F) :
    f ≫ moduleDerivedCoproductFiniteProjection A D F t ∈
      (moduleCompactComparison A D X F).range := by
  rw [moduleDerivedCoproductFiniteProjection, comp_sum]
  apply Submodule.sum_mem
  intro j _
  simpa only [Category.assoc] using
    moduleCompactRange_ι A D F j (f ≫ moduleDerivedCoproductProjection A D F j)

lemma moduleCompact_triangle_obj₃ (T : Triangle (DerivedModuleCategory A D))
    (hT : T ∈ distTriang (DerivedModuleCategory A D))
    (h₁ : moduleCompact A D T.obj₁) (h₂ : moduleCompact A D T.obj₂) :
    moduleCompact A D T.obj₃ := by
  rw [moduleCompact_iff_comparison_surjective]
  intro J F f
  obtain ⟨t, g, hg⟩ := h₂ J F (T.mor₂ ≫ f)
  let p := moduleDerivedCoproductFiniteProjection A D F t
  let q := 𝟙 (∐ F) - p
  have hf : T.mor₂ ≫ (f ≫ q) = 0 := by
    rw [← Category.assoc, ← hg, sum_comp]
    apply Finset.sum_eq_zero
    intro j hj
    rw [Category.assoc]
    change g j ≫ (Sigma.ι F j ≫
      (𝟙 (∐ F) - moduleDerivedCoproductFiniteProjection A D F t)) = 0
    rw [moduleDerivedCoproductComplement_mem A D F t j hj, comp_zero]
  obtain ⟨a, ha⟩ := Triangle.yoneda_exact₃ T hT (f ≫ q) hf
  have hsplit : f = f ≫ p + T.mor₃ ≫ a := by
    rw [← ha]
    dsimp only [q]
    rw [comp_sub, Category.comp_id]
    abel
  change f ∈ (moduleCompactComparison A D T.obj₃ F).range
  rw [hsplit]
  exact Submodule.add_mem _ (moduleCompactRange_finiteProjection A D F t f)
    (moduleCompactRange_precompose A D (moduleCompact_shift A D h₁ 1) F T.mor₃ a)

instance moduleCompactTriangulatedClosed₃ : (moduleCompact A D).IsTriangulatedClosed₃ :=
  ObjectProperty.IsTriangulatedClosed₃.mk' (moduleCompact_triangle_obj₃ A D)

instance moduleCompactTriangulatedClosed₂ : (moduleCompact A D).IsTriangulatedClosed₂ :=
  ObjectProperty.IsTriangulatedClosed₂.of_isTriangulatedClosed₃

instance moduleCompactContainsZero : (moduleCompact A D).ContainsZero :=
  ⟨⟨0, isZero_zero _, moduleCompact_of_isZero A D (isZero_zero _)⟩⟩

instance moduleCompactIsTriangulated : (moduleCompact A D).IsTriangulated := by
  constructor

end SerrePositivity.DifferentialGraded
