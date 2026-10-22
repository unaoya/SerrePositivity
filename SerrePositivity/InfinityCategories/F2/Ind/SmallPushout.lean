module

public import SerrePositivity.InfinityCategories.F2.Ind.KappaSmallRange
public import SerrePositivity.InfinityCategories.F2.SmallSubcomplexCovers
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.SetTheory.Cardinal.HasCardinalLT
public import Mathlib.CategoryTheory.Adhesive.Basic

/-!
概要：単射に沿う小さい二図式の pushout は κ-small。
方針：両像が全単体を覆うことを評価余極限で示し、非退化単体の濃度を抑える。
規約：正則 κ と元の pushout を保持。使われ方：射の二段補間領域の小ささ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 元の pushout の各単体は左右いずれかの脚の像。 -/
lemma pushout_simplex_covered {A B C : SSet.{u}} (f : A ⟶ B) (g : A ⟶ C)
    (n : SimplexCategoryᵒᵖ) (x : (pushout f g).obj n) :
    (∃ b, (pushout.inl f g).app n b = x) ∨ ∃ c, (pushout.inr f g).app n c = x := by
  have hc := isColimitOfPreserves ((evaluation _ (Type u)).obj n) (pushoutIsPushout f g)
  obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit hc x
  rcases j with _ | b
  · exact Or.inl ⟨f.app n y, hy⟩
  · cases b with
    | left => exact Or.inl ⟨y, hy⟩
    | right => exact Or.inr ⟨y, hy⟩

/-- 単射に沿う κ-small な二部品の元の pushout は κ-small。 -/
lemma isKappaSmall_pushout_of_mono {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    {A B C : SSet.{u}} (f : A ⟶ B) (g : A ⟶ C) [Mono f] [Mono g]
    (hB : IsKappaSmall κ B) (hC : IsKappaSmall κ C) :
    IsKappaSmall κ (pushout f g) := by
  haveI : Mono (pushout.inl f g) :=
    Adhesive.mono_of_isPushout_of_mono_right (IsPushout.of_hasPushout f g)
  haveI : Mono (pushout.inr f g) :=
    Adhesive.mono_of_isPushout_of_mono_left (IsPushout.of_hasPushout f g)
  let R : ULift.{u} Bool → (pushout f g).Subcomplex := fun b =>
    if b.down then Subcomplex.range (pushout.inl f g) else Subcomplex.range (pushout.inr f g)
  have hR : ∀ b, IsKappaSmall κ (R b) := by
    intro b
    rcases b with ⟨b⟩
    cases b with
    | false => exact isKappaSmall_range_of_mono _ hC
    | true => exact isKappaSmall_range_of_mono _ hB
  have hcover : ⨆ b, R b = ⊤ := by
    ext n x
    simp only [Subfunctor.iSup_obj, Set.mem_iUnion, Subfunctor.top_obj, Set.mem_univ, iff_true]
    rcases pushout_simplex_covered f g n x with ⟨b, hb⟩ | ⟨c, hc⟩
    · exact ⟨ULift.up true, ⟨b, hb⟩⟩
    · exact ⟨ULift.up false, ⟨c, hc⟩⟩
  exact isKappaSmall_of_cover hκ
    ((hasCardinalLT_iff_cardinal_mk_lt _ _).mp
      (hasCardinalLT_of_finite _ _ hκ.aleph0_le)) R hR hcover

end SerrePositivity.InfinityCategories.F2.Ind
