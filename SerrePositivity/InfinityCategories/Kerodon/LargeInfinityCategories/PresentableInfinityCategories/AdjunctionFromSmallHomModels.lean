module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.AccessibleCorepresentability
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.AdjunctionFromHomRepresentation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallHomCompositeContinuity

/-!
概要：accessible な極限保存 Hom 模型から元の関手の左随伴を構成する。
方針：d3 の余表現可能性を各小さい Hom 関手へ適用し、comma 始対象で全随伴を組み立てる。
規約：左随伴や大域単位の存在は入力に含めない。
使われ方：随伴関手定理における小さい Hom 模型と一般の存在判定の接続。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：各 Hom 合成に accessible な極限保存の小さい模型があれば元の左随伴が存在する。
方針：各模型を元の対象で余表現し、元の全 Hom 比較を通して随伴を組み立てる。
規約：小さい模型の比較は全自然同型で要求する。
使われ方：一般の極限保存関手の随伴の存在。 -/
lemma exists_leftAdjoint_of_accessible_limitPreserving_HomModels
    {X Y : SSet.{u + 1}} [Quasicategory X] [Quasicategory Y]
    (G : Y ⟶ X) (hYa : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessible Y) (hYl : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallLimits Y)
    (h : ∀ x : X _⦋0⦌, ∃ H : Y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u},
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessibleFunctor H ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesSmallLimits H ∧
        Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
          ((SSet.uliftFunctor.{u + 2, u + 1}).map G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.covariantRepresentableInfinity x)
          ((SSet.uliftFunctor.{u + 2, u + 1}).map H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.spaceUniverseDiagram))) :
    ∃ F : X ⟶ Y, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.exists_leftAdjoint_of_covariantHom_representable G
  intro x
  obtain ⟨H, hHa, hHl, ⟨hH⟩⟩ := h x
  obtain ⟨y, ⟨hy⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.accessible_preservesLimits_isCorepresentable H hYa hYl hHa hHl
  exact ⟨y, ⟨hy ≪≫ hH.symm⟩⟩

/-- 概要：反映界面の下で accessible な極限保存関手の各 Hom 合成の小さい連続模型を得る。
方針：元の Hom の小さい模型を合成し、同じ濃度と極限保存を反映する。
規約：宇宙変更の充満忠実性を明示し、無条件の随伴関手定理とは区別する。
使われ方：Compact から供給される反映界面による最終接続。 -/
lemma accessible_limitPreservingHomModels_of_spaceUniverseFullyFaithful
    {X Y : SSet.{u + 1}} [Quasicategory X]
    (hU : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.spaceUniverseDiagram.{u}) (hX : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessible X)
    (G : Y ⟶ X) (hGa : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessibleFunctor G) (hGl : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesSmallLimits G) :
    ∀ x : X _⦋0⦌, ∃ H : Y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u},
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessibleFunctor H ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesSmallLimits H ∧
        Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
          ((SSet.uliftFunctor.{u + 2, u + 1}).map G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.covariantRepresentableInfinity x)
          ((SSet.uliftFunctor.{u + 2, u + 1}).map H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.spaceUniverseDiagram)) := by
  intro x
  obtain ⟨H, ⟨hH⟩⟩ := hX.exists_smallCovariantHom x
  exact ⟨G ≫ H, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallHomComposite_isAccessible hU hX G hGa x H hH,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallHomComposite_preservesSmallLimits hU G hGl x H hH, ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallHomCompositeIso G x H hH⟩⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
