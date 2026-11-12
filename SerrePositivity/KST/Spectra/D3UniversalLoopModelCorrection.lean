module

public import SerrePositivity.KST.Spectra.D3DoubleEndpointSourcePasting

/-!
概要：保持した二方向実模型比較と単位の差を、点つき Kan の全関手上で固定する。
方針：元の全図式比較を合成し、指定二方向始点比較の差との厳密な関係を証明する。
規約：補正の恒等性や反転との一致は仮定しない。円交換因子は直接比較しない。
使われ方：段ごとの補正の幾何的な実証対象を同じ普遍比較の上に固定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra

/-- 同じ実標的への二つの単位貼合せは、元の補正を指定始点比較の差へ移す。 -/
lemma d3Iso_difference_via_common_target {V : Type v} [Category V]
    {P Q F G T : V} (u : P ≅ F) (c : F ≅ G) (w : P ≅ G)
    (x : F ≅ T) (y : G ≅ T) (a : P ≅ Q) (l r : Q ≅ T)
    (hc : c ≪≫ y = x) (hu : u ≪≫ x = a ≪≫ l) (hw : w ≪≫ y = a ≪≫ r) :
    (u ≪≫ c) ≪≫ w.symm = (a ≪≫ (l ≪≫ r.symm)) ≪≫ a.symm := by
  calc
    _ = (u ≪≫ (c ≪≫ y)) ≪≫ (w ≪≫ y).symm := by
      simp only [Iso.trans_symm, Iso.trans_assoc, Iso.self_symm_id_assoc]
    _ = (a ≪≫ l) ≪≫ (a ≪≫ r).symm := by rw [hc, hu, hw]
    _ = _ := by simp only [Iso.trans_symm, Iso.trans_assoc]

namespace OmegaSpectrum.AdjointLoopRelativeBF

/-- 同じ二方向実模型への接続から回収する、全入力上の指定模型比較。 -/
def d3DoubleEndpointLoopImageComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso d3LoopedSectionFamily.{u}
      (pointedKanLoopInfinity ≫ d3PointedKanLoopSection) :=
  d3LoopedSectionLeftDiagramIso ≪≫ d3CanonicalImageLeftDiagramIso.symm

/-- 二つの元の実模型接続を、同じ比較から全図式で厳密回収する。 -/
lemma d3DoubleEndpointLoopImageComparison_recover :
    d3DoubleEndpointLoopImageComparison.{u} ≪≫ d3CanonicalImageLeftDiagramIso =
      d3LoopedSectionLeftDiagramIso := by
  simp only [d3DoubleEndpointLoopImageComparison, Iso.trans_assoc,
    Iso.symm_self_id, Iso.trans_refl]

/-- 元の looped 単位と canonical image 単位の差を、同じ全入力上に保持する。 -/
def d3DoubleEndpointLoopModelCorrection :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (pointedKanLoopInfinity.{u} ≫ pointedKanLoopInfinity)
      (pointedKanLoopInfinity ≫ pointedKanLoopInfinity) :=
  (d3LoopedSectionUnitIso ≪≫ d3DoubleEndpointLoopImageComparison.postcomp
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0)) ≪≫ d3CanonicalImageUnitIso.symm

/-- 保持した単位補正は、同じ二方向実面始点比較の差を元の端点表示で移した値。 -/
lemma d3DoubleEndpointLoopModelCorrection_value :
    d3DoubleEndpointLoopModelCorrection.{u} =
      (d3PointedKanEndpointLoopIso.postcomp pointedKanLoopInfinity ≪≫
        d3DoubleEndpointSourceDifference) ≪≫
          (d3PointedKanEndpointLoopIso.postcomp pointedKanLoopInfinity).symm := by
  apply d3Iso_difference_via_common_target _ _ _
    (d3LoopedSectionLeftDiagramIso.postcomp (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0))
    (d3CanonicalImageLeftDiagramIso.postcomp (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0))
  · rw [← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_trans, d3DoubleEndpointLoopImageComparison_recover]
  · exact d3LoopedSectionLeftDiagramIso_unit_pasting_endpoint
  · exact d3CanonicalImageLeftDiagramIso_unit_pasting

end OmegaSpectrum.AdjointLoopRelativeBF
end SerrePositivity.KST.Spectra
