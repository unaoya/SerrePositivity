module

public import SerrePositivity.KST.Spectra.D3StagePullback
public import SerrePositivity.KST.Spectra.D3CommonLoopSquare

/-!
概要：構成済み実 loop 錐そのものの、全 coherent 段評価後の極限性。
方針：同じ実 BF 引き戻し錐の段極限性を、同じ cospan 上の極限錐の一意性で移す。
規約：同じ元の錐・比較辺を保持する。段別極限から BF 全体の自然性は推論しない。
使われ方：d3b② の実 loop 図式の始点作用と元の補助標的の段比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
local instance d3LoopConeStageSpectrumCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance d3LoopConeStageSpectrumHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := mappingSpace_kanComplex X Y

/-- 同じ元の実 BF fiber 錐の段極限性から、同じ cospan の全実極限錐を評価する。 -/
lemma d3FiberCone_stage_isLimit {E B : OmegaSpectrum.{u}} (p : E ⟶ B)
    [∀ k, Fibration (p.app k).right]
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPullbackDiagram p (fromPoint B))))
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (c.postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3StageKanEnriched n))) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.isLimitCone_postcomp_of_one_limitCone _
    (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPullbackInfinityCone p (fromPoint B))
    (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPullbackInfinityCone_isLimit p (fromPoint B)) _ c hc
  exact d3StagePullbackInfinityCone_isLimit p (fromPoint B) n

/-- 同じ実錐の図式 cast は、実際の後合成と可換。 -/
lemma d3Cone_cast_postcomp {K X Y : SSet.{u + 1}} {p q : K ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (h : p = q) (F : X ⟶ Y) :
    (c.cast h).postcomp F = (c.postcomp F).cast (congrArg (· ≫ F) h) := by
  subst q
  rfl

/-- 元の錐の形状制限と後合成は、同じ join 射全体で厳密に交換する。 -/
lemma d3Cone_restrict_postcomp {K L X Y : SSet.{u + 1}} {p : K ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (i : L ⟶ K) (F : X ⟶ Y) :
    (DiagramLimitTransport.restrict c i).postcomp F =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.coherentConeRestrict (c.postcomp F) i).cast (Category.assoc i p F).symm := by
  apply Subtype.ext
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u + 1})) i ≫ c.val) ≫ F =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u + 1})) i ≫ (c.val ≫ F)
  exact Category.assoc _ _ _

/-- 元の BasedLoop 錐そのものを全 coherent 段評価しても極限錐。 -/
lemma d3BasedLoopCone_stage_isLimit (Y : OmegaSpectrum.{u}) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone ((BasedLoop.cone Y).postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3StageKanEnriched n))) := by
  rw [BasedLoop.cone, d3Cone_cast_postcomp]
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.coherentConeCast_isLimit_iff _ _).2
  rw [d3Cone_restrict_postcomp]
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.coherentConeCast_isLimit_iff _ _).2
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.coherentConeRestrict_isLimit_iff _ CospanShape.strictCospanHornIso.inv).1
  exact d3FiberCone_stage_isLimit (basedPathProjection Y) _
    (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPullbackInfinityCone_isLimit (basedPathProjection Y) (fromPoint Y)) n

/-- 同じ元の固定 cospan 上の任意の実極限錐も、同じ段評価で極限になる。 -/
lemma d3BasedLoopDiagramCone_stage_isLimit (Y : OmegaSpectrum.{u})
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (BasedLoop.diagram Y)) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (c.postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3StageKanEnriched n))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.isLimitCone_postcomp_of_one_limitCone _ (BasedLoop.cone Y)
    (BasedLoop.cone_isLimit Y) (d3BasedLoopCone_stage_isLimit Y n) c hc

/-- 同じ実 loop 始点錐を段評価した実錐の極限性。 -/
lemma loopSourceCone_stage_isLimit (X : OmegaSpectrum.{u}) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone ((loopSourceCone X).postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3StageKanEnriched n))) :=
  d3BasedLoopDiagramCone_stage_isLimit (tail X) _ (loopSourceCone_isLimit X) n

/-- 同じ共通 BF 対象上の実錐を段評価した実錐の極限性。 -/
lemma commonLoopCone_stage_isLimit (X : OmegaSpectrum.{u}) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone ((commonLoopCone X).postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3StageKanEnriched n))) :=
  d3BasedLoopDiagramCone_stage_isLimit (tail X) _ (commonLoopCone_isLimit X) n

/-- 元の実共通四角形全体の段評価は、点つき Kan ∞ 圏の実引き戻し四角形。 -/
lemma commonLoopSquare_stage_isPullback (X : OmegaSpectrum.{u}) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare ((commonLoopSquare X).square ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3StageKanEnriched n)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare_isPullback _ (commonLoopCone_stage_isLimit X n)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare (commonLoopCone X) ≫ _) at ⊢
  convert h using 1
  exact Category.assoc _ _ _

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
