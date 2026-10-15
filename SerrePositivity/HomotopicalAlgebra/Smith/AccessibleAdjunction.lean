module

public import SerrePositivity.HomotopicalAlgebra.Smith.AccessibleColimits
public import Mathlib.CategoryTheory.Presentable.Dense
public import Mathlib.CategoryTheory.Presentable.Adjunction
public import Mathlib.CategoryTheory.Presentable.SharplyLT.Lemmas

/-! # Accessibility of right adjoints between accessible categories

A dense family of presentable objects detects filtered-colimit preservation.
The adjunction moves each detecting Hom to a representable in the source.
Only the image of the essentially small dense family needs a common bound;
no accessibility claim about a general full image is made.
-/

@[expose] public section
universe w v₀ u₀ v v' u u'
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite

namespace SerrePositivity.Smith.AccessibleAdjunction
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

include adj in
lemma rightAdjoint_isCardinalAccessible_of_dense
    {B : Type u₀} [Category.{v₀} B] (a : B ⥤ C) [a.IsDense]
    (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [∀ b, IsCardinalPresentable (a.obj b) κ]
    [∀ b, IsCardinalPresentable (F.obj (a.obj b)) κ] : G.IsCardinalAccessible κ := by
  let E := Presheaf.restrictedULiftYoneda.{v'} a
  have hE : E.IsCardinalAccessible κ := by
    have : ∀ b, (E ⋙ (evaluation Bᵒᵖ (Type (max v v'))).obj b).IsCardinalAccessible κ :=
      fun b ↦ inferInstanceAs
        ((uliftCoyoneda.{v'}.obj (op (a.obj b.unop))).IsCardinalAccessible κ)
    exact AccessibleColimits.functorCategory_isCardinalAccessible E κ
  have hGE : (G ⋙ E).IsCardinalAccessible κ := by
    have : ∀ b, Functor.IsCardinalAccessible
        ((G ⋙ E) ⋙ (evaluation Bᵒᵖ (Type (max v v'))).obj b) κ := by
      intro b
      have : Functor.IsCardinalAccessible
          ((F.op ⋙ uliftCoyoneda.{v}).obj (op (a.obj b.unop))) κ := inferInstanceAs
        ((uliftCoyoneda.{v}.obj (op (F.obj (a.obj b.unop)))).IsCardinalAccessible κ)
      exact Functor.isCardinalAccessible_of_natIso
        ((adj.compUliftCoyonedaIso.{0}).app (op (a.obj b.unop))) κ
    exact AccessibleColimits.functorCategory_isCardinalAccessible (G ⋙ E) κ
  refine ⟨fun J _ _ ↦ ?_⟩
  have := E.preservesColimitsOfShape_of_isCardinalAccessible κ J
  have := (G ⋙ E).preservesColimitsOfShape_of_isCardinalAccessible κ J
  exact preservesColimitsOfShape_of_reflects_of_preserves G E

include adj in
lemma rightAdjoint_isAccessible [IsAccessibleCategory.{w} C] [IsAccessibleCategory.{w} D] :
    G.IsAccessible.{w} := by
  obtain ⟨κ₀, h₀, hC⟩ := IsAccessibleCategory.exists_cardinal.{w} C
  let P := isCardinalPresentable C κ₀
  obtain ⟨μ, hμ, hF⟩ := (P.map F).le_isCardinalPresentable
  obtain ⟨κ, hκ, h₀κ, hμκ⟩ := Cardinal.SharplyLT.exists_of_pair κ₀ μ
  have hp : ∀ b : P.FullSubcategory, IsCardinalPresentable (P.ι.obj b) κ := by
    intro b
    have : IsCardinalPresentable (P.ι.obj b) κ₀ := b.property
    exact isCardinalPresentable_of_le _ h₀κ.le
  have hfp : ∀ b : P.FullSubcategory, IsCardinalPresentable (F.obj (P.ι.obj b)) κ := by
    intro b
    have : IsCardinalPresentable (F.obj (P.ι.obj b)) μ := hF _ (P.prop_map_obj F b.property)
    exact isCardinalPresentable_of_le _ hμκ.le
  have := rightAdjoint_isCardinalAccessible_of_dense adj P.ι κ
  exact G.isAccessible_of_isCardinalAccessible κ

end SerrePositivity.Smith.AccessibleAdjunction
