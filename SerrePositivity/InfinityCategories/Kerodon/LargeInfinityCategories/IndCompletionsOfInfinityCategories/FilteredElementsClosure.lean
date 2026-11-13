module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.OrdinaryFilteredElementsClosure
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredPosetNerve
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalCoconeRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.CofinalUniverseLift
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.RepresentableFilteredElements

/-!
概要：元の right unstraightening の元の圏の κ-filtered 条件は、前層内の全 κ-filtered 余極限で閉じる。
方針：同じ native 余錐を小さい cofinal poset に制限し、構成済みの coherent strict 化の保存を使う。
規約：正則 κ。添字・標的の宇宙を明示し、同じ元の頂点を保持する。
使われ方：HTT 5.3.5.4、最小閉包から right fibration 定義への逆方向。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable (κ : Cardinal.{u}) [Fact κ.IsRegular] (C : SSet.{u}) [Quasicategory C]

/-- 元の right unstraightening の元の圏の κ-filtered 条件は、全ての小さい κ-filtered 余極限で閉じる。 -/
lemma hasKappaFilteredElements_kappaColimitClosed :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IsKappaColimitClosed κ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasKappaFilteredElements κ (C := C)) := by
  intro K hK hFiltered F c hc hF
  obtain ⟨I, o, f, hI, hN, hf⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.exists_cofinal_kappaFiltered_poset (κ := κ) K
  letI := o
  have : IsCardinalFiltered I κ := hI
  let f' := (SSet.uliftFunctor.{u + 1, u}).map f
  have hc' : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (c.restrict f') :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isColimitCone_iff_restrict_rightCofinal f' (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isRightCofinal_ulift f hf) c).mp hc
  have hv := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.hasKappaFilteredElements_of_ordinary_colimit (f' ≫ F) (c.restrict f') hc'
    (fun i => hF (f.app (Opposite.op ⦋0⦌) i))
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex_restrict] using hv

/-- Indκ の最小閉包への所属は、同じ前層の元の right unstraightening の κ-filtered 性と同値。 -/
lemma isIndVertex_iff_hasKappaFilteredElements (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IsIndVertex κ C v ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasKappaFilteredElements κ v := by
  constructor
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isIndVertex_minimal κ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasKappaFilteredElements κ (C := C))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.hasKappaFilteredElements_yoneda κ)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.hasKappaFilteredElements_isoClosed κ C)
      (hasKappaFilteredElements_kappaColimitClosed κ C)
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isIndVertex_of_hasKappaFilteredElements κ

/-- 元の関手で書いた Indκ 条件は、元の right unstraightening の全空間に対する条件そのもの。 -/
lemma isIndVertex_functorVertex_iff
    (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IsIndVertex κ C (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.smallRightUnstraightening F) :=
  (isIndVertex_iff_hasKappaFilteredElements κ C (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F)).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.hasKappaFilteredElements_functorVertex κ F)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "5.3.5.1"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isIndVertex_functorVertex_iff
attribute [cite HTT "5.3.5.4" (partial := component) "仮定：小準圏 C、正則 κ、前層 F（HTT と一致）。結論：(1) 元の表現可能前層の単一 κ-filtered 余極限表示と (2) Indκ 所属が同値（一致）。C が κ-small 余極限を持つ場合の (3) κ-small 極限保存との同値は含まない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isIndVertex_functorVertex_iff
