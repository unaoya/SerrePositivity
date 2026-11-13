module

public import
  SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.SpecifiedCoconeRootEndInitialProjection
public import
  SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.SpecifiedCoconeRootEvaluationHomotopy
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FunctorComparison.FunctorIsoPostcompComposition

/-!
概要：評価固定の初期 Hom 円柱の底の類を、元の指定した初期射影比較の類へ同定する。
方針：三因子の底の相殺・右の raw な底の一致・評価上の忠実性を組み合わせる。
規約：底は同じ射の類として保持する。使われ方：共通 end 内の指定経路の整合性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
attribute [local irreducible] _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitStrictSpanCocone _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitApexSpan
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRootLeg _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftLeg _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightLeg
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (f ≫ (i ≫ p))) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
  (dB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (i ≫ p)) (dC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (j ≫ p)) (y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌)
local notation "q" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (f ≫ (i ≫ p))
local notation "I" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootInitialComparisonIso hp p c hc dB dC y
local notation "HR" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootEndInitialHomotopy hp p c hc dB dC y
local notation "H" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootEvaluationHomotopy hp p c hc dB dC y
local notation "J" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootInitialProjectionComparison hp p c hc dB dC y
local notation "P" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialProjection q c y
local notation "B" => Iso.hom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialBaseIso q c y)
local notation "T" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedPathCocone hp p c hc dB dC)) y

/-- 三比較の合成同型の通常 Hom 表示での底は、元の初期射影比較の同じ射の類。 -/
lemma specifiedCoconeRootInitialComparisonIso_native_hom_arrow :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp I (P ≫ B)).hom =
      Arrow.mk (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy J)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.functorIso_postcomp_hom_arrow_map I (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy HR) P B
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootInitialComparisonIso_base_hom_arrow hp p c hc dB dC y)
  refine h.trans ?_
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyIso_postcomp_hom]
  exact _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomotopy_hom_arrow_of_h_eq (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp HR (P ≫ B)) J
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootEndInitialHomotopy_native_projection hp p c hc dB dC y)

/-- 厳密な評価固定代表の底も、元の指定した初期射影円柱の同じ射の類を持つ。 -/
lemma specifiedCoconeRootEvaluationHomotopy_native_hom_arrow :
    Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H (P ≫ B)))) =
      Arrow.mk (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy J)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootEvaluationHomotopy_hom hp p c hc dB dC y
  have hm := congrArg (hoFunctor.map ((ihom T).map (P ≫ B))).toFunctor.map h
  rw [← _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyIso_postcomp_hom, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.functorIso_postcomp_hom]
  exact (congrArg Arrow.mk hm).trans
    (by simpa only [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.functorIso_postcomp_hom] using
      (specifiedCoconeRootInitialComparisonIso_native_hom_arrow hp p c hc dB dC y))

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
