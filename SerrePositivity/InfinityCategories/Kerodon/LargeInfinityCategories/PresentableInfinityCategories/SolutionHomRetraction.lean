module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PullbackConeClassificationRetraction
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SolutionConeHomComparison
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.GeneratorSolutionCone

/-!
概要：全解錐から元の制限関手を頂点の全共変 Hom の retract として構成する。
方針：元の縮小同型の pullback 表示を使い、全分類図式の retract を元の関手へ移す。
規約：全関手圏内の分裂であり、余表現可能性の結論を追加仮定に置かない。
使われ方：compact 生成対象上の解による余表現可能関手の構成。

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
variable {A : SSet.{u}} {C : SSet.{u + 1}}
  (i : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ C) (F : C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})

/-- 概要：小さい全解の持ち上げは元の unstraightening の厳密な底変換。
方針：元の縮小同型の四角形と unstraightening の底変換を貼り合わせる。
規約：元の全空間と射影を変更しない。
使われ方：全解錐の分類における retract の戻り射。 -/
lemma smallSolutionLift_isPullback :
    IsPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallSolutionLift i F)
      ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection (i ≫ F)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection F) i := by
  have hs := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMap_isPullback (i ≫ F) F i rfl
  have he : IsPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningIso (i ≫ F)).hom
      ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection (i ≫ F)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection (i ≫ F)) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]; exact
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningIso_projection _⟩
  simpa only [Category.id_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallSolutionLift] using he.paste_horiz hs

variable [Quasicategory A] [Quasicategory C]

/-- 概要：元の関手の制限は、全解錐の頂点からの全共変 Hom 制限の retract。
方針：元の底変換の全分類 retract を、縮小同型と coslice 分類同型で移す。
規約：指定された元の錐と頂点を保持する。
使われ方：accessible な極限保存関手の表現可能 retract の存在。 -/
lemma solutionHom_isRetract (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallSolutionLift i F)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 2, u + 1}).map (i ≫ F) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.spaceUniverseDiagram))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 2, u + 1}).map i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.covariantRepresentableInfinity
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection F).app (Opposite.op ⦋0⦌) d.vertex))) := by
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection F).app (Opposite.op ⦋0⦌) d.vertex))
  have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram (pullback.snd q i))
      ((SSet.uliftFunctor.{u + 2, u + 1}).map i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.covariantRepresentableInfinity
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection F).app (Opposite.op ⦋0⦌) d.vertex)) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram_baseChangeIso q i).symm ≪≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.covariantRepresentableInfinity_cosliceIso _).symm
        ((SSet.uliftFunctor.{u + 2, u + 1}).map i)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf.of_iso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallSolutionClassificationIso i F).symm).trans
    ((show _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf _ _ from
      ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.conePullbackClassificationRetraction (smallSolutionLift_isPullback i F) d⟩).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf.of_iso ht))

/-- 概要：accessible な極限保存関手は、小さい compact 生成圏上で生成対象の Hom の retract。
方針：生成解を頂点とする全解錐を取り、同じ全分類 retract を適用する。
規約：元の全関手圏の分裂を結論し、各点での分裂に弱めない。
使われ方：余表現可能性のための冪等分裂と filtered 生成による延長。 -/
lemma exists_accessibleGeneratorHomRetract (hCa : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessible C) (hCl : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallLimits C)
    (hFa : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessibleFunctor F) (hFl : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesSmallLimits F) :
    ∃ (κ : Cardinal.{u}) (A : SSet.{u}) (hA : Quasicategory A),
      letI := hA
      ∃ (i : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ C) (a : A _⦋0⦌),
        κ.IsRegular ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaCompactGenerating κ i ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ F ∧
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 2, u + 1}).map (i ≫ F) ≫
            _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.spaceUniverseDiagram))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 2, u + 1}).map i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.covariantRepresentableInfinity
            (i.app (Opposite.op ⦋0⦌) (ULift.up a)))) := by
  obtain ⟨κ, A, hA, i, hκ, hi, hκF, a, d, hd⟩ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_accessibleGeneratorSolutionCone F hCa hCl hFa hFl
  have := hA
  have h := solutionHom_isRetract i F d
  rw [hd] at h
  exact ⟨κ, A, hA, i, a, hκ, hi, hκF, h⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
