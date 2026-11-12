module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftTransportPostcomp
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeLeftExtension
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeCoconeAbsolute
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitConstantFamily

/-!
概要：一般の U 上の相対左 Kan 単位の可逆性をその像の可逆性から導く。
方針：像の点では後合成した局所余錐が絶対余極限となり、相対条件から元の余極限を回収する。
規約：U は inner fibration。指定単位の像の可逆性を明示する。
使われ方：元と標的の図式を同時に保つ相対 Kan 拡張の厳密化。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：単位の U 像が可逆なら、像の点の局所輸送の U 像は絶対的な余極限。
方針：後合成した輸送を標準余錐との同型とし、像の点での標準余極限性を戻す。
規約：元の局所輸送 t の余錐を後合成したものを判定する。
使われ方：相対局所余極限から指定単位の成分の可逆性を回収する。 -/
lemma kanLeftTransport_image_isColimit_at_image {K C D E : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory E]
    (δ : K ⟶ C) [InnerFibration δ] (hδ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful δ) (U : D ⟶ E)
    {F₀ : K ⟶ D} {F : C ⟶ D} {β : SSet.Homotopy F₀ (δ ≫ F)}
    (hU : IsIso ((hoFunctor.map ((ihom K).map U)).toFunctor.map
      (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy β))))
    (k : K _⦋0⦌) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanCoconeTransport δ F₀ F β (δ.app (Opposite.op ⦋0⦌) k)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanPostcomposeCocone U t.cocone) := by
  let s := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftTransportPostcomp t U
  have hs := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftTransport_isIso_of_unit_isIso s (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftUnitPostcomp_isIso β U hU)
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone s.cocone := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanIsColimitCone_of_functorIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCanonical_isColimit_at_image δ hδ (F ≫ U) k)
    (asIso (SSet.Truncated.HomotopyCategory.homMk s.edge)).symm
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_congr
    (by simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram, Category.assoc])
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanPostcomposeCocone U t.cocone) s.cocone
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftTransportPostcomp_cocone_val t U).symm).2 hc

/-- 概要：相対左 Kan 単位の像が可逆なら元の指定単位も各点で可逆。
方針：像の点で相対余錐と像の絶対余極限性から元の余極限を得て、指定成分へ移す。
規約：終対象上の場合へ仮定を強めず、任意の inner U を扱う。
使われ方：標的も固定する相対厳密化のための指定単位の可逆性。 -/
lemma kanRelativeLeftKanExtension_unit_component_isIso {K C D E : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (δ : K ⟶ C) [InnerFibration δ] (hδ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful δ) (U : D ⟶ E) [InnerFibration U]
    {F₀ : K ⟶ D} {F : C ⟶ D} (β : SSet.Homotopy F₀ (δ ≫ F))
    (hβ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRelativeLeftKanExtension U δ F₀ F β)
    (hU : IsIso ((hoFunctor.map ((ihom K).map U)).toFunctor.map
      (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy β))))
    (k : K _⦋0⦌) :
    IsIso (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate
      (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy β)) k) := by
  obtain ⟨t, ht⟩ := hβ (δ.app (Opposite.op ⦋0⦌) k)
  have himage := kanLeftTransport_image_isColimit_at_image δ hδ U hU k t
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanIsColimitCone_of_relativeLifting_of_image U t.cocone
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanRelativeCoconeLifting_of_isRelativeColimitCone U _ ht) himage
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftTransport_identity_unit_component_isIso δ hδ k t hc

/-- 概要：像が可逆な相対左 Kan 単位は元の h Fun の指定射として可逆。
方針：各点の成分の可逆性を関手圏の辺の可逆性の判定へ渡す。
規約：元の指定変換とその U による像の同じ類を使う。
使われ方：全部分圏包含上の元の図式を保つ相対 Kan 厳密化。 -/
lemma kanRelativeLeftKanExtension_unit_isIso {K C D E : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (δ : K ⟶ C) [InnerFibration δ] (hδ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful δ) (U : D ⟶ E) [InnerFibration U]
    {F₀ : K ⟶ D} {F : C ⟶ D} (β : SSet.Homotopy F₀ (δ ≫ F))
    (hβ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRelativeLeftKanExtension U δ F₀ F β)
    (hU : IsIso ((hoFunctor.map ((ihom K).map U)).toFunctor.map
      (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy β)))) :
    IsIso (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy β)) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy β)
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isInvertibleEdge_iff_evaluateFunctorAt (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy β)).2
  intro k
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomEvaluate_isIso_iff _ k).1
    (kanRelativeLeftKanExtension_unit_component_isIso δ hδ U β hβ hU k)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
