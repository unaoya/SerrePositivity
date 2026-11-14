module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CoherentProductComparisonEdge
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.SpaceBinaryTensorProduct
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.SpecifiedApexConeRestrictions

/-!
概要：coherent 積図式の元の余極限を頂点とする native な二項積錐を作る。
方針：同じ比較辺で標準積錐を輸送し、全錐の円柱とその二制限を保持する。
規約：底図式は元の二つの余極限頂点。使われ方：sifted 余極限の有限積保存。

対応節は Kerodon 9.7（Tag 06ZD）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories
variable {B : SSet.{u}} [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.IsSiftedInfinity B]
  (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})

/-- 元の比較辺の全錐円柱を持つ、元の余極限頂点への指定輸送。 -/
def siftedCoherentProductNativeConeTransport :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.SpecifiedApexLimitConeTransport
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spaceBinaryTensorProductCone (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalKanObject F)
        (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalKanObject G))
      (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProduct F G)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coherentProductComparisonApexPrism F G) :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.specifiedApexLimitConeTransport _ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spaceBinaryTensorProductCone_isLimit _ _) _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coherentProductComparisonApexPrism_zero F G) (by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coherentProductComparisonApexPrism_one]
      apply SSet.yonedaEquiv.injective
      exact (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spaceBinaryTensorProductCone_vertex _ _).symm)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coherentProductComparisonApexPrism_vertical_isInvertible F G)

/-- 元の積図式の余極限頂点を持つ、二つの元の余極限の native な積錐。 -/
def siftedCoherentProductNativeCone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanBinaryDiagram (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalKanObject F) (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalKanObject G))) :=
  (siftedCoherentProductNativeConeTransport F G).cone

/-- 同じ元の頂点と全錐を持つ二項積錐の普遍性。 -/
lemma siftedCoherentProductNativeCone_isLimit :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (siftedCoherentProductNativeCone F G) :=
  (siftedCoherentProductNativeConeTransport F G).isLimit

/-- 輸送した錐の頂点は、積図式の元の余極限頂点と厳密に一致する。 -/
lemma siftedCoherentProductNativeCone_vertex :
    (siftedCoherentProductNativeCone F G).vertex =
      _root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProduct F G) := by
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _ ≫ (siftedCoherentProductNativeCone F G).val) = _
  dsimp only [siftedCoherentProductNativeCone]
  rw [(siftedCoherentProductNativeConeTransport F G).apex_eq, Equiv.apply_symm_apply]

/-- 元の比較辺を頂点に持つ、標準積錐への全錐のホモトピー。 -/
def siftedCoherentProductNativeConeHomotopy :
    SSet.Homotopy (siftedCoherentProductNativeCone F G).val
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spaceBinaryTensorProductCone (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalKanObject F)
        (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalKanObject G)).val :=
  (siftedCoherentProductNativeConeTransport F G).homotopy

/-- 全錐円柱の頂点への制限は、元の指定比較辺の円柱そのもの。 -/
lemma siftedCoherentProductNativeConeHomotopy_apex :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _ ▷ (Δ[1] : SSet.{u + 1})) ≫
      (siftedCoherentProductNativeConeHomotopy F G).h =
        (β_ (Δ[0] : SSet.{u + 1}) (Δ[1] : SSet.{u + 1})).hom ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coherentProductComparisonApexPrism F G :=
  (siftedCoherentProductNativeConeTransport F G).apex

/-- 全錐円柱は、二つの元の余極限頂点の底図式を全時刻で固定する。 -/
lemma siftedCoherentProductNativeConeHomotopy_diagram :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr _ _ ▷ (Δ[1] : SSet.{u + 1})) ≫
      (siftedCoherentProductNativeConeHomotopy F G).h =
        fst _ (Δ[1] : SSet.{u + 1}) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve
          (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanBinaryDiagram (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalKanObject F)
            (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalKanObject G)) :=
  (siftedCoherentProductNativeConeTransport F G).diagram

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "5.5.8.11" (partial := special) "仮定：有限積と K 余極限を持ち積が各変数でそれを保つ準圏（Lean が強い：Space の場合）。結論：coherent 空間図式の元の余極限と二項積・空積の比較が実際の極限錐となる（この場合に有限積保存と一致）。任意 X の積保存を仮定して同じ比較を一般化したとはしない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.siftedCoherentProductNativeCone_isLimit
attribute [cite HTT "5.5.8.12" (partial := component) "仮定：小 sifted K（HTT と一致）。結論：Space の元の coherent K 余極限の積・空積との交換（本文の空間の場合に一致）。任意の ∞-topos で各変数の積が余極限を保存するという後半の拡張は含まない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.siftedCoherentProductNativeCone_isLimit
