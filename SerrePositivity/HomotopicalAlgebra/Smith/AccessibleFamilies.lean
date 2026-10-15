module

public import SerrePositivity.HomotopicalAlgebra.Smith.AccessibleColimits
public import Mathlib.SetTheory.Cardinal.HasCardinalLT

/-! # Common cardinals for small heterogeneous families of accessible functors -/

@[expose] public section
universe w t v u v' u' s
noncomputable section
open CategoryTheory

namespace SerrePositivity.Smith

/-- Constant functors with independent source and target categories. -/
lemma constant_isCardinalAccessible {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (X : C) (κ : Cardinal.{w}) [Fact κ.IsRegular] :
    ((Functor.const D).obj X).IsCardinalAccessible κ where
  preservesColimitOfShape J _ _ :=
    { preservesColimit {F} :=
        { preserves {c} hc := ⟨by
            have h := isFiltered_of_isCardinalFiltered J κ
            have (j : J) : IsIso ((((Functor.const D).obj X).mapCocone c).ι.app j) := by
              dsimp
              infer_instance
            exact Functor.IsEventuallyConstantFrom.isColimitOfIsIso
              (i₀ := h.nonempty.some) (fun _ _ ↦ by dsimp; infer_instance) _⟩ } }

/-- Sources and targets may vary with the index. The bound is common to
the whole small family, including all finite stages of a construction. -/
lemma exists_common_accessibility {ι : Type t} [Small.{w} ι]
    {C : ι → Type u} [∀ i, Category.{v} (C i)]
    {D : ι → Type u'} [∀ i, Category.{v'} (D i)]
    (F : ∀ i, C i ⥤ D i) [∀ i, (F i).IsAccessible.{w}] :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular), ∀ i, (F i).IsCardinalAccessible κ := by
  choose κ hκ hF using fun i ↦ Functor.IsAccessible.exists_cardinal (F i)
  obtain ⟨μ, hμ, hb⟩ := HasCardinalLT.exists_regular_cardinal_forall
    (fun i ↦ (κ i).ord.ToType)
  have : Fact μ.IsRegular := ⟨hμ⟩
  refine ⟨μ, inferInstance, fun i ↦ ?_⟩
  have h := hb i
  simp only [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_toType, Cardinal.card_ord] at h
  exact (F i).isCardinalAccessible_of_le h.le

lemma functorCategory_isAccessible {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] {K : Type t} [Category.{s} K] [Small.{w} K]
    (F : D ⥤ K ⥤ C)
    [∀ k, (F ⋙ (evaluation K C).obj k).IsAccessible.{w}] : F.IsAccessible.{w} := by
  obtain ⟨κ, hκ, h⟩ := exists_common_accessibility
    (fun k ↦ F ⋙ (evaluation K C).obj k)
  have := AccessibleColimits.functorCategory_isCardinalAccessible F κ
  exact F.isAccessible_of_isCardinalAccessible κ

end SerrePositivity.Smith
