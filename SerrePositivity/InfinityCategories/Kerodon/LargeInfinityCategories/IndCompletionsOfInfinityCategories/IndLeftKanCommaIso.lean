module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndLeftKanShapeAmbient
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.YonedaSlice

/-!
概要：Indκ 内の左 Kan 局所添字と、元の前層の Yoneda comma の同じ射影を同定する。
方針：全部分圏の添字同型に、元の頂点の表示変更と引き戻しの因子交換を合成する。
規約：元の C の宇宙持ち上げへの射影を厳密に保つ。
使われ方：元の小さい元の圏を Indκ の局所 Kan 添字の模型として使う。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 局所添字の頂点表示を等式で変えても、元の始域への射影は変わらない。 -/
lemma leftKanShapeTransport_projection {K X : SSet.{u}} (δ : K ⟶ X)
    {v w : X _⦋0⦌} (h : v = w) :
    eqToHom (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape δ) h) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection δ w =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection δ v := by
  subst w
  rfl

variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C] (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C) _⦋0⦌)

/-- 同じ Indκ 頂点での左 Kan 局所添字と、元の前層の Yoneda comma の厳密な同型。 -/
def indLeftKanCommaIso : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C) v ≅
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.presheafYonedaSlice (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indVertexPresheaf κ v) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indLeftKanShapeAmbientIso κ v ≪≫
    eqToIso (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C)) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indVertexPresheaf_vertex κ v).symm) ≪≫
    pullbackSymmetry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indVertexPresheaf κ v))))

/-- 同じ comma 同型は、元の C への射影を厳密に保つ。 -/
lemma indLeftKanCommaIso_hom_projection :
    (indLeftKanCommaIso κ v).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.presheafYonedaSliceProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indVertexPresheaf κ v) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C) v := by
  simp only [indLeftKanCommaIso, Iso.trans_hom, eqToIso.hom, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.presheafYonedaSliceProjection, pullbackSymmetry_hom_comp_snd]
  have ht := leftKanShapeTransport_projection (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indVertexPresheaf_vertex κ v).symm
  exact (congrArg (fun f => (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indLeftKanShapeAmbientIso κ v).hom ≫ f) ht).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indLeftKanShapeAmbientIso_hom_projection κ v)

/-- 同じ逆同型も、元の C への射影を厳密に保つ。 -/
lemma indLeftKanCommaIso_inv_projection :
    (indLeftKanCommaIso κ v).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C) v =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.presheafYonedaSliceProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indVertexPresheaf κ v) := by
  rw [← indLeftKanCommaIso_hom_projection, (indLeftKanCommaIso κ v).inv_hom_id_assoc]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
