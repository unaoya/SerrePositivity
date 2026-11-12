module

public import SerrePositivity.KST.Spectra.D3StageLoopSquare
public import SerrePositivity.KST.Spectra.D3CommonLoopDiagramSection
public import SerrePositivity.KST.Spectra.D3CommonStageLoop

/-!
概要：構成済みの全実 loop 図式族を、同じ全単体のまま各段の実 loop 図式族へ移す。
方針：元の図式族を段評価で後合成し、各頂点の同じ段四角形の実証から全部分圏へ因子化。
規約：始点・終点の全関手を厳密保持。各段から BF 全体の比較は推論しない。
使われ方：d3b② の実図式始点の段作用を元の右射影の段自然性へ接続する基底。
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
local instance d3LoopFamilyStageSpectrumCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 四角形頂点の実際の図式を取り出す操作は後合成と交換する。 -/
lemma d3SquareDiagram_postcomp {X Y : SSet.{u + 1}}
    (v : ((ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).obj X) _⦋0⦌) (F : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram (((ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).map F).app _ v) =
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v ≫ F := by
  obtain ⟨S, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1]) X).surjective v
  change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (S ≫ F)) = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex S) ≫ F
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagram_functorVertex, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagram_functorVertex]

/-- 四角形の全パラメータに対し、各角の評価は後合成と厳密に交換。 -/
lemma d3SquareEvaluation_postcomp {X Y : SSet.{u + 1}} (F : X ⟶ Y)
    (k : ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1]) _⦋0⦌) :
    (ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).map F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k ≫ F := rfl

/-- 元の全実図式族を段評価した、同じ全四角形族。 -/
def commonChosenStageSquareFamily (n : ℕ) :
    SimplicialNerve CommonObject.{u} ⟶
      (ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).obj PointedKanInfinity :=
  commonChosenLoopDiagramFamily ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).ι ≫
    (ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3StageKanEnriched n))

/-- 全族の各頂点の四角形は、元の構成済み実四角形の同じ段評価そのもの。 -/
lemma commonChosenStageSquareFamily_vertex (n : ℕ)
    (v : (SimplicialNerve CommonObject.{u}) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram ((commonChosenStageSquareFamily n).app _ v) =
      (commonLoopSquare_stage (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject v).val n).square := by
  change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram (((ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3StageKanEnriched n))).app _
      (commonChosenLoopDiagramFamily.app _ v).val) = _
  rw [d3SquareDiagram_postcomp, commonChosenLoopDiagramFamily_square_vertex]
  rfl

/-- 同じ全族は、各頂点で実際の零角と引き戻し性を持つ。 -/
lemma commonChosenStageSquareFamily_isLoop (n : ℕ)
    (v : (SimplicialNerve CommonObject.{u}) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex ((commonChosenStageSquareFamily n).app _ v) := by
  unfold _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex
  rw [commonChosenStageSquareFamily_vertex]
  exact ⟨(commonLoopSquare_stage _ n).zero_corner,
    (commonLoopSquare_stage _ n).other_zero, (commonLoopSquare_stage _ n).isPullback⟩

/-- 元の全実 loop 図式族の、同じ全単体を保つ各段の実 loop 図式族。 -/
def commonChosenStageLoopDiagramFamily (n : ℕ) :
    SimplicialNerve CommonObject.{u} ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams PointedKanInfinity :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex (commonChosenStageSquareFamily n)
    (commonChosenStageSquareFamily_isLoop n)

/-- 四つの角の全関手を、元の全図式族の同じ角の段評価として回収する。 -/
lemma commonChosenStageLoopDiagramFamily_corner (n : ℕ) (i j : Fin 2) :
    commonChosenStageLoopDiagramFamily.{u} n ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity i j =
      (commonChosenLoopDiagramFamily ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation Sp.{u} i j) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3StageKanEnriched n) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation, commonChosenStageLoopDiagramFamily]
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι]
  change (commonChosenLoopDiagramFamily ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).ι ≫
    (ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3StageKanEnriched n))) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt _ = _
  rw [Category.assoc, Category.assoc, d3SquareEvaluation_postcomp]
  simp only [Category.assoc]

/-- 全実段図式族の始点は、元の同じ始点関手の段評価そのもの。 -/
lemma commonChosenStageLoopDiagramFamily_source (n : ℕ) :
    commonChosenStageLoopDiagramFamily.{u} n ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0 =
      commonChosenLoopSource ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3StageKanEnriched n) :=
  commonChosenStageLoopDiagramFamily_corner n 0 0

/-- 全実段図式族の終点は、元の厳密 nativeTail 終点関手の同じ段評価。 -/
lemma commonChosenStageLoopDiagramFamily_target (n : ℕ) :
    commonChosenStageLoopDiagramFamily.{u} n ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1 =
      commonNativeLoopEndpoint ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3StageKanEnriched n) := by
  rw [commonChosenStageLoopDiagramFamily_corner, commonChosenLoopDiagramFamily_target]

/-- 元の tail と段評価は、同じ全 Hom 上で厳密に添字移動する。 -/
lemma d3StageTail_enriched (n : ℕ) :
    tailEnriched.comp SSet (d3StageKanEnriched.{u} n) = d3StageKanEnriched (n + 1) := by
  apply EnrichedFunctor.ext SSet
  case h_obj =>
    intro X
    rfl
  case h_map =>
    intro X Y
    simp only [eqToHom_refl, Category.comp_id]
    exact tailMapping_evaluation X Y n

/-- 同じ全単体上で nativeTail の段評価は元の次段評価に一致。 -/
lemma d3StageTail (n : ℕ) :
    nativeTail.{u} ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3StageKanEnriched n) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3StageKanEnriched (n + 1)) := by
  rw [nativeTail, ← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp, d3StageTail_enriched]

/-- 段 loop 図式族の厳密終点は、元の共通 BF 基底の同じ次段評価である。 -/
lemma commonChosenStageLoopDiagramFamily_target_next (n : ℕ) :
    commonChosenStageLoopDiagramFamily.{u} n ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1 =
      commonOriginalInfinityMap ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3StageKanEnriched (n + 1)) := by
  rw [commonChosenStageLoopDiagramFamily_target, commonNativeLoopEndpoint,
    Category.assoc, d3StageTail]

/-- 元の右射影の全関手比較を、同じ実段図式族の厳密終点で表示する。
右辺が同じ終点の通常 loop であることを全単体で保持。実図式始点との比較は残る。 -/
def commonChosenStageEndpointLoopIso (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap commonRefinedEnriched ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3StageKanEnriched n))
      ((commonChosenStageLoopDiagramFamily.{u} n ≫
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1) ≫ pointedKanLoopInfinity) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (commonStageLoopFunctorIso n) rfl
    (by rw [commonChosenStageLoopDiagramFamily_target_next])

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
