module

public import SerrePositivity.KST.Spectra.D3CommonCoherentComparison
public import SerrePositivity.KST.Spectra.AdjointLoopRelativeDiagramResolution

/-!
概要：比較射を含む同じ共通 BF 基底に、厳密 tail 上の全実 loop 図式を記憶する。
方針：元の終点評価を共通 BF 基底に沿って実際に引き戻す。
規約：図式始点と共通 BF 対象の全 Hom 整合はまだ課していない。
使われ方：d3b② の図式・BF 比較を同じ基底で照合する入口。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
local instance commonLoopDiagramSpectrumCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance commonLoopDiagramHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := OmegaSpectrum.mappingSpace_kanComplex X Y

/-- 共通 BF 基底から元の full 基底への同じ全単体射影。 -/
def commonBaseInfinityMap : SimplicialNerve CommonObject ⟶ SimplicialNerve FullObject :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap commonBaseEnriched

/-- 共通 BF 基底でも終点は元の対象の nativeTail。 -/
def commonNativeLoopEndpoint : SimplicialNerve CommonObject ⟶ Sp.{u} :=
  commonOriginalInfinityMap ≫ nativeTail

lemma commonBaseInfinityMap_endpoint :
    commonBaseInfinityMap.{u} ≫ fullNativeLoopEndpoint = commonNativeLoopEndpoint := by
  rw [fullNativeLoopEndpoint, ← Category.assoc]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap commonBaseEnriched ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap fullOriginalEnriched) ≫
    nativeTail = _
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp]
  rfl

lemma commonNativeLoopEndpoint_vertex (X : CommonObject.{u}) :
    commonNativeLoopEndpoint.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (tail X.val) := by
  change nativeTail.app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap commonOriginalEnriched).app _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex]
  exact nativeTail_vertex X.val

/-- 同じ全単体で実 loop 図式と共通 BF 比較を記憶する基底。
図式始点と refined 関手を結ぶ全 Hom 条件は未追加。 -/
def commonLoopDiagramResolution : SSet.{u + 1} :=
  pullback (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation Sp.{u} 1 1) commonNativeLoopEndpoint

def commonLoopDiagramProjection :
    commonLoopDiagramResolution.{u} ⟶ SimplicialNerve CommonObject :=
  pullback.snd _ _

def commonLoopDiagramFamily : commonLoopDiagramResolution.{u} ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams Sp.{u} :=
  pullback.fst _ _

lemma commonLoopDiagramFamily_target :
    commonLoopDiagramFamily.{u} ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation Sp.{u} 1 1 =
      commonLoopDiagramProjection ≫ commonNativeLoopEndpoint :=
  pullback.condition

/-- 図式を忘れて同じ共通 BF 基底へ戻る射影の実全単射 RLP。
始点 BF 関手との整合を追加した射影に対する主張ではない。 -/
instance commonLoopDiagramProjection_trivialKanFibration :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration commonLoopDiagramProjection.{u} :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.pullback_snd _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem
    (p := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation Sp.{u} 1 1))⟩

instance commonLoopDiagramResolution_quasicategory :
    Quasicategory commonLoopDiagramResolution.{u} :=
  quasicategory_of_innerFibration commonLoopDiagramProjection

def commonLoopDiagramEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence commonLoopDiagramResolution.{u} (SimplicialNerve CommonObject) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOfTrivialKanFibration commonLoopDiagramProjection

/-- 元の BF 比較族と既存の部分 loop 図式を同時に保つ全単射相対充填。
新しい部分の図式始点と refined 関手の一致は、この充填の条件に含めない。 -/
lemma exists_relative_commonLoopDiagram {V U : SSet.{u + 1}} (j : V ⟶ U) [Mono j]
    (a : V ⟶ commonLoopDiagramResolution.{u})
    (b : U ⟶ SimplicialNerve CommonObject)
    (h : a ≫ commonLoopDiagramProjection = j ≫ b) :
    ∃ d : U ⟶ commonLoopDiagramResolution,
      j ≫ d = a ∧ d ≫ commonLoopDiagramProjection = b ∧
        (d ≫ commonLoopDiagramFamily) ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation Sp.{u} 1 1 =
          b ≫ commonNativeLoopEndpoint := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := commonLoopDiagramProjection) j inferInstance
  let sq : CommSq a j commonLoopDiagramProjection b := ⟨h⟩
  refine ⟨sq.lift, sq.fac_left, sq.fac_right, ?_⟩
  rw [Category.assoc, commonLoopDiagramFamily_target, ← Category.assoc, sq.fac_right]

/-- 同じ共通 BF 全単体を固定した図式選択の fiber は可縮。 -/
lemma commonLoopDiagramFiber_isContractibleKan
    (v : (SimplicialNerve CommonObject.{u}) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber commonLoopDiagramProjection v) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_isContractibleKan commonLoopDiagramProjection v

/-- 元の full 図式基底にも、同じ図式・元の BF 比較を保って戻る。 -/
def commonLoopDiagramToFull :
    commonLoopDiagramResolution.{u} ⟶ fullLoopDiagramResolution :=
  pullback.lift commonLoopDiagramFamily
    (commonLoopDiagramProjection ≫ commonBaseInfinityMap) (by
      rw [Category.assoc, commonBaseInfinityMap_endpoint]
      exact commonLoopDiagramFamily_target)

@[reassoc (attr := simp)]
lemma commonLoopDiagramToFull_projection :
    commonLoopDiagramToFull.{u} ≫ fullLoopDiagramResolutionProjection =
      commonLoopDiagramProjection ≫ commonBaseInfinityMap :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
lemma commonLoopDiagramToFull_family :
    commonLoopDiagramToFull.{u} ≫ fullLoopDiagramResolutionFamily = commonLoopDiagramFamily :=
  pullback.lift_fst _ _ _

/-- 同じ共通 BF 比較を保ち、元の Sp まで戻る実同値。 -/
def commonLoopDiagramOriginalEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence commonLoopDiagramResolution.{u} Sp.{u} :=
  commonLoopDiagramEquivalence.trans commonOriginalInfinityEquivalence

/-- 共通 BF 図式上の refined 関手。図式始点への同一視は別途必要。 -/
def commonLoopDiagramRefinedMap : commonLoopDiagramResolution.{u} ⟶ Sp.{u} :=
  commonLoopDiagramProjection ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap commonRefinedEnriched

/-- 元の二段包含は同じ図式基底上でも全関手同型を与える。 -/
def commonLoopDiagramInclusionIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (commonLoopDiagramProjection.{u} ≫ commonOriginalInfinityMap)
      commonLoopDiagramRefinedMap :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp commonInclusionFunctorIso commonLoopDiagramProjection

/-- 同じ基底で、元の比較右脚を成分とする全 BF 図式比較も保持する。 -/
def commonLoopDiagramComparisonIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso commonLoopDiagramRefinedMap.{u}
      (commonLoopDiagramProjection ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap commonMiddleEnriched) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp commonComparisonFunctorIso commonLoopDiagramProjection

/-- 同じ図式基底で、記憶した全図式を元の指定 native 図式族と比較する。 -/
def commonLoopDiagramNativeIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso commonLoopDiagramFamily.{u}
      ((commonLoopDiagramProjection ≫ commonNativeLoopEndpoint) ≫
        nativeLoopTargetEquivalence.inv) :=
  nativeLoopDiagramFamilyIso _ _ (by
    rw [Category.assoc, nativeLoopTargetEquivalence_inv_target, Category.comp_id]
    exact commonLoopDiagramFamily_target)

/-- 記憶した実図式の始点と元の nativeLoop の全関手比較。
refined 関手との比較には、さらに同じ全 Hom 上の整合が必要。 -/
def commonLoopDiagramSourceNativeIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (commonLoopDiagramFamily.{u} ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation Sp.{u} 0 0)
      ((commonLoopDiagramProjection ≫ commonNativeLoopEndpoint) ≫ nativeLoop) := by
  have e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp commonLoopDiagramNativeIso (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation Sp.{u} 0 0)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso _ _ at e
  simpa only [Category.assoc, nativeLoop] using e

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
