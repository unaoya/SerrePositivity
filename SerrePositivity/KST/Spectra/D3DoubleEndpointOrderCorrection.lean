module

public import SerrePositivity.KST.Spectra.D3DoubleEndpointOrderModels
public import SerrePositivity.KST.Spectra.D3UniversalLoopModelStages

/-!
概要：保持した模型補正を、同じ全四次元比較の始点作用そのものへ接続する。
方針：同じ左右始点表示の貼合せを元の指定全入力補正へ代入する。
規約：始点作用を反転と同一視しない。使われ方：主対象の補正一致の幾何的検査。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF

/-- 全四次元比較の同じ始点作用を、保持した実右面の厳密始点へ表示する。 -/
def d3DoubleEndpointOrderRealSourceIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (d3DoubleEndpointRightLoopFamily.{u} 0 0 ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0)
      (d3DoubleEndpointRightLoopFamily 0 0 ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (d3DoubleEndpointOrderFaceSourceIso 0 0)
    (d3DoubleEndpointRightLoopFamily_corner 0 0 0 0).symm
    (d3DoubleEndpointRightLoopFamily_corner 0 0 0 0).symm

/-- 全四次元比較の同じ始点作用は、元の左右実面始点比較をそのまま接続する。 -/
lemma d3DoubleEndpointOrderRealSourceIso_pasting :
    d3LeftDoubleEndpointSourceIso.{u} ≪≫ d3DoubleEndpointOrderRealSourceIso =
      d3RightDoubleEndpointSourceIso := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorIso_trans_heq_of_heq rfl
    (d3DoubleEndpointRightLoopFamily_corner 0 0 0 0).symm
    (d3DoubleEndpointRightLoopFamily_corner 0 0 0 0).symm
    (d3DoubleEndpointLeftSourceIso.{u} 0 0) (d3DoubleEndpointOrderFaceSourceIso 0 0)
    d3LeftDoubleEndpointSourceIso d3DoubleEndpointOrderRealSourceIso
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _)
  have hr : HEq d3RightDoubleEndpointSourceIso.{u} (d3DoubleEndpointRightSourceIso.{u} 0 0) :=
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _).symm
  exact eq_of_heq (h.trans ((heq_of_eq (d3DoubleEndpointOrderFaceSourceIso_pasting 0 0)).trans
    hr.symm))

/-- 左右実面始点比較の差は、全四次元比較の同じ始点作用の逆を移した指定値。 -/
lemma d3DoubleEndpointSourceDifference_order_value :
    d3DoubleEndpointSourceDifference.{u} =
      (d3LeftDoubleEndpointSourceIso ≪≫ d3DoubleEndpointOrderRealSourceIso.symm) ≪≫
        d3LeftDoubleEndpointSourceIso.symm := by
  unfold d3DoubleEndpointSourceDifference
  rw [← d3DoubleEndpointOrderRealSourceIso_pasting, Iso.trans_symm, Iso.trans_assoc]

/-- 元の端点表示と左始点比較を、同じ実四次元始点への指定単位として保持する。 -/
def d3DoubleEndpointTotalUnitIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (pointedKanLoopInfinity.{u} ≫ pointedKanLoopInfinity)
      (d3DoubleEndpointRightLoopFamily 0 0 ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0) :=
  d3PointedKanEndpointLoopIso.postcomp pointedKanLoopInfinity ≪≫ d3LeftDoubleEndpointSourceIso

/-- 保持した全入力模型補正は、同じ全四次元比較の始点作用の逆を移した値そのもの。 -/
lemma d3DoubleEndpointLoopModelCorrection_order_value :
    d3DoubleEndpointLoopModelCorrection.{u} =
      (d3DoubleEndpointTotalUnitIso ≪≫ d3DoubleEndpointOrderRealSourceIso.symm) ≪≫
        d3DoubleEndpointTotalUnitIso.symm := by
  rw [d3DoubleEndpointLoopModelCorrection_value, d3DoubleEndpointSourceDifference_order_value]
  simp only [d3DoubleEndpointTotalUnitIso, Iso.trans_symm, Iso.trans_assoc]

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
