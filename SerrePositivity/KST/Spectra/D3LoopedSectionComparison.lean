module

public import SerrePositivity.KST.Spectra.D3DoubleEndpointLoopImageComparison
public import SerrePositivity.KST.Spectra.D3StageLoopedCanonical

/-!
概要：元の厳密 loop 切断の通常 loop 像を、指定二方向実面へ全図式比較する。
方針：元の切断補正の同じ比較を通常 loop へ写し、共同模型から得た実比較へ合成する。
規約：切断や標準単位を選び直さず、一般的な loop 保存性も新仮定にしない。
使われ方：保持済みの各段 looped canonical 族を二方向実端点図式へ接続する。
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

/-- 元の端点実図式の包含は、元の端点パラメータ全四角形に厳密一致する。 -/
lemma d3PointedKanEndpointLoopDiagram_ι :
    d3PointedKanEndpointLoopDiagram.{u} ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).ι = d3EndpointParameterSquare :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

/-- 元の厳密切断へ通常 loop を施した同じ全四角形族。 -/
def d3LoopedSectionSquare : PointedKanInfinity.{u} ⟶
    (ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).obj PointedKanInfinity :=
  (d3PointedKanLoopSection ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).ι) ≫
    (ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).map pointedKanLoopInfinity

/-- 元の切断補正の同じ比較の loop 像を、元の端点全図式の loop 像へ接続する。 -/
def d3LoopedSectionSquareIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso d3LoopedSectionSquare.{u}
      (d3EndpointParameterSquare ≫
        (ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).map pointedKanLoopInfinity) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (d3PointedKanLoopSection_diagramIso.postcomp
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).ι ≫
      (ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).map pointedKanLoopInfinity))
    (Category.assoc _ _ _).symm
    (by rw [← Category.assoc, d3PointedKanEndpointLoopDiagram_ι])

/-- 元の厳密切断の loop 像は、認証した同じ実図式との比較から実 loop 図式を持つ。 -/
lemma d3LoopedSectionSquare_isLoop (v : PointedKanInfinity.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex (d3LoopedSectionSquare.app _ v) := by
  have e := d3LoopedSectionSquareIso.{u}.toNatIso.app (SSet.HomotopyCategory.mk v)
  apply (d3IsLoopDiagramVertex_iso e).mpr
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex ((d3EndpointParameterSquare ≫
    (ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).map pointedKanLoopInfinity).app _ v)
  exact d3EndpointParameterSquare_loop_isLoop v

/-- 同じ厳密切断の通常 loop 像を、全 Hom・全単体を保って実 loop 図式へ制限。 -/
def d3LoopedSectionFamily : PointedKanInfinity.{u} ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams PointedKanInfinity :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex d3LoopedSectionSquare d3LoopedSectionSquare_isLoop

lemma d3LoopedSectionFamily_ι :
    d3LoopedSectionFamily.{u} ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).ι =
      d3LoopedSectionSquare := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

/-- 同じ通常 loop 像の四角は、元の厳密切断の同じ角へ通常 loop を施した値。 -/
lemma d3LoopedSectionFamily_corner (i j : Fin 2) :
    d3LoopedSectionFamily.{u} ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity i j =
      (d3PointedKanLoopSection ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity i j) ≫
        pointedKanLoopInfinity := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation]
  rw [← Category.assoc, d3LoopedSectionFamily_ι]
  dsimp only [d3LoopedSectionSquare]
  rw [Category.assoc, d3SquareEvaluation_postcomp]
  simp only [Category.assoc]

/-- この同じ loop 像の終点は、通常 loop 関手に厳密一致する。 -/
lemma d3LoopedSectionFamily_target :
    d3LoopedSectionFamily.{u} ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1 =
      pointedKanLoopInfinity := by
  rw [d3LoopedSectionFamily_corner, d3PointedKanLoopSection_target, Category.id_comp]

/-- 同じ切断補正の loop 像を、実 loop 全図式上の同じ比較として回収する。 -/
def d3LoopedSectionDiagramIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso d3LoopedSectionFamily.{u} d3EndpointLoopImageFamily :=
  (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι
    ((ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).obj PointedKanInfinity)
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).preimageFunctorIso
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq d3LoopedSectionSquareIso
          d3LoopedSectionFamily_ι.symm d3EndpointLoopImageFamily_ι.symm)

/-- 元の厳密切断の loop 像から、第一パラメータが端点円である実面へ全図式比較。 -/
def d3LoopedSectionLeftDiagramIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso d3LoopedSectionFamily.{u} (d3DoubleEndpointRightLoopFamily 0 0) :=
  d3LoopedSectionDiagramIso ≪≫ d3DoubleEndpointLeftLoopImageDiagramIso

/-- 第二パラメータが端点円である他方の実面へも、同じ切断の比較を保持する。 -/
def d3LoopedSectionRightDiagramIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso d3LoopedSectionFamily.{u} (d3DoubleEndpointLeftLoopFamily 0 0) :=
  d3LoopedSectionDiagramIso ≪≫ d3DoubleEndpointRightLoopImageDiagramIso

/-- 保持済み段標準族の loop 像は、同じ厳密切断の loop 像への元の終点前合成。 -/
lemma commonChosenStageLoopedCanonicalFamily_section (n : ℕ) :
    (commonChosenStageLoopDiagramFamily.{u} (n + 1) ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1) ≫ d3LoopedSectionFamily =
      commonChosenStageLoopedCanonicalFamily n := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).ι).1
  rw [Category.assoc, d3LoopedSectionFamily_ι, commonChosenStageLoopedCanonicalFamily_ι]
  simp only [d3LoopedSectionSquare, commonChosenStageLoopedCanonicalSquareFamily,
    commonChosenStageCanonicalFamily, Category.assoc]

/-- 保持済みの段 looped canonical 全図式を、同じ終点入力の二方向実面へ接続。 -/
def commonChosenStageLoopedCanonicalDoubleEndpointIso (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (commonChosenStageLoopedCanonicalFamily.{u} n)
      ((commonChosenStageLoopDiagramFamily (n + 1) ≫
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1) ≫ d3DoubleEndpointRightLoopFamily 0 0) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (d3LoopedSectionLeftDiagramIso.precomp
    (commonChosenStageLoopDiagramFamily (n + 1) ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1))
    (commonChosenStageLoopedCanonicalFamily_section n) rfl

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
