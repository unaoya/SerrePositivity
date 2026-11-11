module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ColimitFromLocalLeftKan
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftCommaCoconeColimit
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftHomUniversal
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitDiagramIso

/-!
概要：元の図式とその全左 Kan 延長の余極限の存在を比較する。
方針：同じ comma の相対 join の両端で全余錐の同値を使い、元の延長との同型で戻す。
規約：どちらの余極限の存在も相手の仮定に混入させない。
使われ方：P_Σ 内の表現可能生成図式と、その次数・密度余極限の比較。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：全余錐制限の同値は余極限の存在を両方向に移す。
方針：普遍余錐の制限と同値の逆による存在を合わせる。
規約：指定図式と同じ制限を使う。
使われ方：相対 join の両端における余極限の存在の比較。 -/
lemma hasColimit_iff_restrict_of_sliceUnderEquivalence
    {A B X : SSet.{u}} [Quasicategory X] (i : A ⟶ B) (F : B ⟶ X)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict F i)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit F ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (i ≫ F) := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c.restrict i, (he.choose.isInitialVertex_iff c).mp hc⟩
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.hasColimit_of_sliceUnderRestrict_equivalence i F he

/-- 概要：comma の普遍な候補の余極限の存在は元の図式の余極限の存在と同値。
方針：相対 join の普遍な左端・任意の右端・元の comma 包含の三つの同値を合成する。
規約：候補の元の左端の等式と全 fiber の普遍性を明示する。
使われ方：任意の指定左 Kan 延長への余極限の存在の移送。 -/
lemma leftCommaCandidate_hasColimit_iff
    {A B X : SSet.{u}} [Quasicategory A] [Quasicategory B] [Quasicategory X]
    (δ : A ⟶ B) (F : A ⟶ X)
    (H : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) (𝟙 B) ⟶ X)
    (hH : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) (𝟙 B) ≫ H =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaSource δ ≫ F)
    (hcol : ∀ b, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinFiberCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) b H)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaCandidate δ H) ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit F := by
  have hr := hasColimit_iff_restrict_of_sliceUnderEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) (𝟙 B)) H
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.relativeJoinRight_sliceUnderRestrict_equivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) H)
  have hl := hasColimit_iff_restrict_of_sliceUnderEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) (𝟙 B)) H
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.sliceUnderRestrict_isQCatEquivalence_of_initialBoundary H _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinFunctor_initialBoundary_of_colimit_fibers
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) H hcol))
  rw [hH] at hl
  have hs := hasColimit_iff_restrict_of_sliceUnderEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaInclusion δ) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaSource δ ≫ F)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.commaSource_sliceUnderRestrict_equivalence δ F)
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaInclusion δ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaSource δ ≫ F) = F := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaInclusion_source, Category.id_comp]
  rw [he] at hs
  exact hr.symm.trans (hl.trans hs)

/-- 概要：元の全左 Kan 延長の余極限の存在は、元の図式の余極限の存在と同値。
方針：同じ局所余極限で構成した comma 候補と指定延長の関手同型を使う。
規約：元の指定単位を保った左 Kan 条件を入力とする。
使われ方：bar 図式の反映と simplicial Ind 表示への接続。 -/
lemma hasColimit_iff_leftKanExtension
    {A B X : SSet.{u}} [Quasicategory A] [Quasicategory B] [Quasicategory X]
    (δ : A ⟶ B) {F : A ⟶ X} {G : B ⟶ X}
    (β : SSet.Homotopy F (δ ≫ G)) (hβ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension δ F G β) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit G ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit F := by
  have hlocal : ∀ b, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram δ F b) := by
    intro b
    obtain ⟨c, hc, _⟩ := hβ.colimitValue b
    exact ⟨c, hc⟩
  obtain ⟨H, hH, _, hcol⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanLeftComma_candidate δ F hlocal
  let γ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaCandidateTransformation δ F H hH
  have hγ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaCandidate_isLeftKanExtension δ F H hH hcol
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftKanExtensionIso δ γ β hγ hβ
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.hasColimit_iff_of_functorIso e).symm.trans
    (leftCommaCandidate_hasColimit_iff δ F H hH hcol)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
