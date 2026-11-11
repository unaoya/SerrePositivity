module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndHomWeightRealization
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CoYonedaColimitExistence

/-!
概要：同じ前層の密度表示と実現可能な Ind 表示から元の標的図式の余極限を作る。
方針：共通の全 Hom 係数族を Ind 実現で表現し、密度の Hom 極限へ移す。
規約：全標的係数の自然性を保ち、余極限存在を追加入力にしない。
使われ方：filtered 余極限と幾何学的実現のみを持つ標的への P_Σ 延長。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


/-- 概要：表現可能密度表示と同じ Ind 表示の延長像が実現できれば元の図式に余極限がある。
方針：全 Hom 極限の表現可能性を二つの表示間で移し、充満忠実な co-Yoneda で戻す。
規約：図式も標的も同じ元の宇宙へ戻して結論する。
使われ方：P_Σ の局所左 Kan 図式の存在。 -/
lemma hasColimit_of_indPresentation_realization (κ : Cardinal.{u})
    {C : SSet.{u}} [Quasicategory C] {D : SSet.{u + 1}} [Quasicategory D]
    {F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D} {G : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C ⟶ D}
    (β : SSet.Homotopy F₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C ≫ G))
    (hβ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C) F₀ G β)
    {E : SSet.{u}} (p : E ⟶ C)
    (cY : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C))
    (hcY : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone cY)
    {J : SSet.{u}} (R : (SSet.uliftFunctor.{u + 1, u}).obj J ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C)
    (cP : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (R ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indInclusionPresheaf κ C)) (hcP : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone cP)
    (eP : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso cP.vertex cY.vertex)
    (cD : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (R ≫ G)) (hcD : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone cD) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit ((SSet.uliftFunctor.{u + 1, u}).map p ≫ F₀) := by
  obtain ⟨dY, hdY, hvY⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_homWeight_yonedaPresentation_limit F₀ p cY hcY
  obtain ⟨e⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indHomWeight_realization_representable κ β hβ R cP hcP cD hcD
  let eP' := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.liftVertexIso.{u + 2, u + 3} ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.liftVertexIso.{u + 1, u + 2} eP).op)
  let ew := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map eP' (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.fullPresheafHomWeightFamily F₀)
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homInfinityCovariant (C := (SSet.uliftFunctor.{u + 2, u + 1}).obj D)
        (ULift.up cD.vertex))) dY.vertex :=
    e ≪≫ ew ≪≫ (eqToIso (congrArg HomotopyCategory.mk hvY)).symm
  have hcol : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit ((SSet.uliftFunctor.{u + 2, u + 1}).map
      ((SSet.uliftFunctor.{u + 1, u}).map p ≫ F₀)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.hasColimit_of_coyoneda_limit_representable _ dY hdY ⟨ULift.up cD.vertex, ⟨he⟩⟩
  exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.hasColimit_iff_ulift _).mpr hcol

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
