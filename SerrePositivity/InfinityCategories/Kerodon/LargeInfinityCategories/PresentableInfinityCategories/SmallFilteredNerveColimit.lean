module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallDiagramFactorization
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
概要：小さい filtered 部分 poset の nerve を包含順に組み立て、元の nerve を回収する。
方針：全鎖を含む部分集合を選び、各次数で型の filtered 余極限の普遍性を検査する。
規約：SSet の通常の余極限を証明する。∞ 圏の余極限や部分余極限の組立ては別途必要。
使われ方：濃度変更の coherent な部分図式の厳密な貼り合わせ。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

variable (κ μ : Cardinal.{u}) [Fact κ.IsRegular] (I : Type u) [PartialOrder I]

/-- 元の部分 poset の nerve と包含が与える、一つの厳密な図式。 -/
def smallFilteredNerveDiagram : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces κ μ I ⥤ SSet.{u} where
  obj A := nerve A.val
  map f := nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.subsetTransition (leOfHom f))
  map_id A := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact CategoryTheory.Functor.ext (fun _ ↦ rfl) (fun _ _ _ ↦ Subsingleton.elim _ _)
  map_comp f g := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact CategoryTheory.Functor.ext (fun _ ↦ rfl) (fun _ _ _ ↦ Subsingleton.elim _ _)

/-- 全ての部分図式を、元の nerve へ厳密に含める余錐。 -/
def smallFilteredNerveCocone : Cocone (smallFilteredNerveDiagram κ μ I) where
  pt := nerve I
  ι :=
    { app A := nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.subsetInclusion A.val)
      naturality := fun A B f ↦ by
        change nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.subsetTransition (leOfHom f)) ≫
          nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.subsetInclusion B.val) = nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.subsetInclusion A.val) ≫ 𝟙 _
        rw [Category.comp_id]
        exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.nerveMap_subsetTransition_inclusion (leOfHom f) }

variable {κ μ I} [Fact μ.IsRegular] [IsCardinalFiltered I κ]

/-- 元の nerve は、同じ小さい filtered 部分 poset の nerve の通常の SSet 余極限。 -/
def smallFilteredNerveCocone_isColimit (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound κ μ) :
    IsColimit (smallFilteredNerveCocone κ μ I) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.smallFilteredPieces_isCardinalFiltered h (I := I)
  have := isFiltered_of_isCardinalFiltered (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces κ μ I) μ
  refine evaluationJointlyReflectsColimits _ (fun n ↦ ?_)
  apply Types.FilteredColimit.isColimitOf'
  · intro s
    have hs : HasCardinalLT (Set.range s.obj) μ :=
      hasCardinalLT_of_finite _ _ (Cardinal.IsRegular.aleph0_le (Fact.out : μ.IsRegular))
    obtain ⟨A, hA⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.exists_smallFilteredPiece_containing h (Set.range s.obj) hs
    let t : (nerve A.val).obj n :=
      { obj i := ⟨s.obj i, hA (Set.mem_range_self i)⟩
        map f := homOfLE (leOfHom (s.map f)) }
    refine ⟨A, t, ?_⟩
    exact CategoryTheory.Functor.ext (fun _ ↦ rfl) (fun _ _ _ ↦ Subsingleton.elim _ _)
  · intro A s t hst
    have he : s = t := by
      apply (mono_iff_injective
        ((nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.subsetInclusion A.val)).app n)).mp inferInstance
      exact hst
    exact ⟨A, 𝟙 A, congrArg _ he⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
