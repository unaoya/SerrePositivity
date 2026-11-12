module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.Accessible
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallFilteredNerveColimit

/-!
概要：元の大きい標的への図式の、小さい filtered 部分図式とその native な余極限。
方針：同じ包含を宇宙 u+1 へ持ち上げ、accessibility の余極限存在条件を適用する。
規約：部分表示は元の全図式の厳密な制限。部分余極限の μ-compact 性は仮定しない。
使われ方：濃度変更で生成候補となる小さい部分余極限。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

variable {κ μ : Cardinal.{u}} [Fact κ.IsRegular]
  {I : Type u} [PartialOrder I] {C : SSet.{u + 1}}

/-- 元の全図式を、同じ filtered 部分 poset に制限した図式。 -/
def smallFilteredPartialDiagram
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ C)
    (A : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces κ μ I) :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve A.val) ⟶ C :=
  (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.subsetInclusion A.val)) ≫ D

/-- κ-filtered 余極限が存在すれば、元の図式の各部分図式も同じ native な余極限を持つ。 -/
lemma smallFilteredPartialDiagram_hasColimit
    (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HasSmallKappaFilteredColimits κ C)
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ C)
    (A : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces κ μ I) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (smallFilteredPartialDiagram D A) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.smallFilteredPiece_nerve_isKappaFiltered A
  exact hC (nerve A.val) (smallFilteredPartialDiagram D A)

/-- 元の μ-small な部分図式は、native な余極限を持つ小さい filtered 制限を厳密に通る。 -/
lemma exists_smallFiltered_partialColimit [Fact μ.IsRegular] [IsCardinalFiltered I κ]
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound κ μ) (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HasSmallKappaFilteredColimits κ C)
    {K : SSet.{u}} (hK : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ K) (a : K ⟶ nerve I)
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ C) :
    ∃ (A : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces κ μ I) (b : K ⟶ nerve A.val),
      (SSet.uliftFunctor.{u + 1, u}).map b ≫ smallFilteredPartialDiagram D A =
        (SSet.uliftFunctor.{u + 1, u}).map a ≫ D ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ (nerve A.val) ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (smallFilteredPartialDiagram D A) := by
  obtain ⟨A, b, hb, _, hA⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_smallFilteredPiece_factorization h hK a
  refine ⟨A, b, ?_, hA, smallFilteredPartialDiagram_hasColimit hC D A⟩
  dsimp only [smallFilteredPartialDiagram]
  rw [← Category.assoc, ← Functor.map_comp, hb]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
