module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.FilteredElementsClosure

/-!
概要：Indκ の対象は、元の小さい元の圏上の単一 κ-filtered 表現可能図式の余極限である。
方針：最小閉包と元の right unstraightening 条件の同値を、同じ canonical 密度余錐に適用する。
規約：正則 κ。元の前層頂点を厳密に保ち、反復閉包の存在で表示を代用しない。
使われ方：HTT 5.3.5.4 と、κ-filtered 余極限を保つ延長の構成。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable (κ : Cardinal.{u}) [Fact κ.IsRegular] (C : SSet.{u}) [Quasicategory C]

/-- 一つの小さい κ-filtered 図式からの、指定した前層頂点そのものを持つ表現可能生成表示。 -/
def HasSingleFilteredRepresentablePresentation (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C) _⦋0⦌) : Prop :=
  ∃ (I : SSet.{u}) (hI : Quasicategory I),
    letI := hI
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ I ∧
    ∃ a : I ⟶ C, ∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone
      ((SSet.uliftFunctor.{u + 1, u}).map a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C),
      c.vertex = v ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c

/-- 任意の Indκ 頂点は、元の right unstraightening 上の同じ密度余錐による単一表示を持つ。 -/
lemma isIndVertex_has_singleFilteredPresentation {v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C) _⦋0⦌}
    (hv : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IsIndVertex κ C v) : HasSingleFilteredRepresentablePresentation κ C v := by
  let F := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinityObjectEquiv C).symm v
  have hF : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F = v := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinityObjectEquiv C).apply_symm_apply v
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IsIndVertex κ C (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) := hF.symm ▸ hv
  have hk := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isIndVertex_functorVertex_iff κ C F).mp hi
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.smallRightUnstraightening F, inferInstance, hk,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.smallRightUnstraighteningProjection F, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityCocone F, ?_,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion.presheafDensityCocone_isColimit F⟩
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityCocone_vertex F).trans hF

/-- 単一の小さい κ-filtered 表現可能表示を持つ前層は、Indκ の最小閉包に属する。 -/
lemma isIndVertex_of_singleFilteredPresentation {v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C) _⦋0⦌}
    (hv : HasSingleFilteredRepresentablePresentation κ C v) : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IsIndVertex κ C v := by
  obtain ⟨I, hI, hκ, a, c, hc, hcol⟩ := hv
  have := hI
  have := hκ
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isIndVertex_kappaColimitClosed κ C I
    ((SSet.uliftFunctor.{u + 1, u}).map a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C) c hcol
    (fun i => _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isIndVertex_yoneda κ (a.app (Opposite.op ⦋0⦌) i))
  exact hc ▸ h

/-- 最小 κ-filtered 閉包は、単一の小さい κ-filtered 表現可能生成表示の条件と同値。 -/
lemma isIndVertex_iff_singleFilteredPresentation (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IsIndVertex κ C v ↔ HasSingleFilteredRepresentablePresentation κ C v :=
  ⟨isIndVertex_has_singleFilteredPresentation κ C,
    isIndVertex_of_singleFilteredPresentation κ C⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "5.3.5.4" (partial := component) "仮定：小準圏 C、正則 κ、前層 F（HTT と一致）。結論：(1) 元の表現可能前層の単一 κ-filtered 余極限表示と (2) Indκ 所属が同値（一致）。C が κ-small 余極限を持つ場合の (3) κ-small 極限保存との同値は含まない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isIndVertex_iff_singleFilteredPresentation
