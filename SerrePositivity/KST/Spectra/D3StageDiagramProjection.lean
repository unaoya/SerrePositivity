module

public import SerrePositivity.KST.Spectra.D3StageLoopStructureFamily
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FullyFaithfulNormalizedIsoRecovery
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TrivialKanFunctorIsoProjection

/-!
概要：既存の段 loop 図式比較と構造同型を、同じ指定射影後の値まで回収する。
方針：充満忠実な逆像の回収則と、実可縮 fiber 内で選んだ同型の射影則を使う。
規約：任意の同型へ置き換えず、既存の全図式比較の値を検査する。
使われ方：refined 段比較と元の段間構造の正方形の照合。
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
local instance d3DiagramProjectionSpectrumCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 回収した実 loop 全図式の構造同型は、周囲の四角形へ戻すと元の指定値そのもの。 -/
lemma commonChosenStageStructureDiagramIso_projection (n : ℕ) :
    HEq ((commonChosenStageStructureDiagramIso.{u} n).postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).ι)
        (commonChosenStageStructureSquareIso n) :=
  (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι
    ((ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).obj PointedKanInfinity)
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).preimageNormalizedFunctorIso_postcomp_heq
        (commonChosenStageLoopDiagramFamily n) (commonChosenStageLoopImageFamily n)
        (commonChosenStageStructureSquareIso n)
        (commonChosenStageLoopDiagramFamily_ι n).symm
        (commonChosenStageLoopImageFamily_ι n).symm

/-- 同じ実 fiber 内比較の終点射影は、指定厳密等式の同型へ戻る。 -/
lemma commonChosenStageCanonicalDiagramIso_target (n : ℕ) :
    (commonChosenStageCanonicalDiagramIso.{u} n).postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1) =
        eqToIso (congrArg
          (fun v : SimplicialNerve CommonObject.{u} ⟶ PointedKanInfinity ↦
            SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex v))
          (commonChosenStageCanonicalFamily_target n).symm) := by
  let := d3PointedKanLoopEvaluation_trivial.{u}
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.functorIsoOfTrivialKanFibration_postcomp
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1)
    (commonChosenStageLoopDiagramFamily n) (commonChosenStageCanonicalFamily n)
    (commonChosenStageCanonicalFamily_target n).symm


/-- 既存の始点比較は、同じ全図式比較と同じ標準 loop 表示同型を合成した値そのもの。 -/
lemma commonChosenStageSourceLoopIso_diagram_triangle (n : ℕ) :
    HEq ((commonChosenStageSourceLoopIso.{u} n) ≪≫
      d3PointedKanLoopSection_sourceIso.precomp
        (commonChosenStageLoopDiagramFamily n ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1))
      ((commonChosenStageCanonicalDiagramIso n).postcomp
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0)) := by
  dsimp only [commonChosenStageSourceLoopIso]
  rw [Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]
  exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _


/-- 同じ全図式比較の始点を、元の実始点段の表示にだけ正規化した指定同型。 -/
def commonChosenStageSourceCanonicalIso (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (commonChosenLoopSource ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3StageKanEnriched.{u} n))
      (commonChosenStageCanonicalFamily n ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq
    ((commonChosenStageCanonicalDiagramIso n).postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0))
    (commonChosenStageLoopDiagramFamily_source n) rfl

/-- 元の始点 loop 比較へ同じ標準表示同型を戻すと、指定全図式の始点比較を回収する。 -/
lemma commonChosenStageSourceLoopIso_canonical (n : ℕ) :
    commonChosenStageSourceLoopIso.{u} n ≪≫
      d3PointedKanLoopSection_sourceIso.precomp
        (commonChosenStageLoopDiagramFamily n ≫
          _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1) =
      commonChosenStageSourceCanonicalIso n := by
  dsimp only [commonChosenStageSourceLoopIso, commonChosenStageSourceCanonicalIso]
  rw [Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]

/-- refined／実始点比較と指定全図式の始点比較は、元の右射影の同じ三角形を満たす。 -/
lemma commonChosenStageRefinedSourceIso_canonical_triangle (n : ℕ) :
    commonChosenStageRefinedSourceIso.{u} n ≪≫ commonChosenStageSourceCanonicalIso n =
      commonChosenStageEndpointLoopIso n ≪≫
        d3PointedKanLoopSection_sourceIso.precomp
          (commonChosenStageLoopDiagramFamily n ≫
            _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1) := by
  rw [← commonChosenStageSourceLoopIso_canonical]
  let a := commonChosenStageEndpointLoopIso.{u} n
  let b := commonChosenStageSourceLoopIso.{u} n
  let c := d3PointedKanLoopSection_sourceIso.precomp
    (commonChosenStageLoopDiagramFamily.{u} n ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1)
  change (a ≪≫ b.symm) ≪≫ (b ≪≫ c) = a ≪≫ c
  calc
    _ = a ≪≫ (b.symm ≪≫ b) ≪≫ c := by simp only [Iso.trans_assoc]
    _ = _ := by simp only [Iso.symm_self_id, Iso.refl_trans]

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
