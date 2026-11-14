module

public import SerrePositivity.KST.Spectra.D3CommonLoopDiagramResolution
public import SerrePositivity.KST.Spectra.D3CommonLoopSquare
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.VertexDiscrete

/-!
概要：構成済み共通実 loop 四角形を全頂点で固定した、共通 BF 基底上の全図式族。
方針：離散全頂点の単射に元の終点評価の実 RLP を適用する。
規約：始点は頂点では元の共通 BF 対象。始点関手の全 Hom 比較は未証明。
使われ方：d3b② で点別選択を保ったまま、残る始点自然性を全図式の上で照合する。
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
local instance commonLoopSectionSpectrumCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance commonLoopSectionHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := OmegaSpectrum.mappingSpace_kanComplex X Y

/-- 各頂点で保持するのは、構成した同じ共通実四角形全体。 -/
def commonChosenLoopVertex (v : (SimplicialNerve CommonObject.{u}) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams Sp.{u}) _⦋0⦌ :=
  (commonLoopSquare (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject v).val).diagramVertex

lemma commonChosenLoopVertex_target (v : (SimplicialNerve CommonObject.{u}) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation Sp.{u} 1 1).app _ (commonChosenLoopVertex v) =
      commonNativeLoopEndpoint.app _ v := by
  rw [commonChosenLoopVertex, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopSquare.diagramVertex_evaluation]
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (commonLoopSquare (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject v).val).square 1 1 = _
  rw [(commonLoopSquare (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject v).val).target_eq]
  exact (commonNativeLoopEndpoint_vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject v)).symm.trans
    (congrArg (fun z ↦ commonNativeLoopEndpoint.app _ z) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object v))

/-- 全頂点の指定四角形と、元の厳密終点族の実可換四角形。 -/
lemma commonChosenLoopLiftSquare : CommSq
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteMap commonChosenLoopVertex.{u})
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteι (SimplicialNerve CommonObject.{u}))
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation Sp.{u} 1 1) commonNativeLoopEndpoint :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteMap_comp _ _ commonChosenLoopVertex commonChosenLoopVertex_target⟩

/-- 各頂点の同じ実四角形を保つ、全単体上の実 loop 図式族。 -/
def commonChosenLoopDiagramFamily : SimplicialNerve CommonObject.{u} ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams Sp.{u} := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation Sp.{u} 1 1)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteι (SimplicialNerve CommonObject.{u})) inferInstance
  exact commonChosenLoopLiftSquare.lift

lemma commonChosenLoopDiagramFamily_vertices :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteι (SimplicialNerve CommonObject.{u}) ≫ commonChosenLoopDiagramFamily =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteMap commonChosenLoopVertex := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation Sp.{u} 1 1)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteι (SimplicialNerve CommonObject.{u})) inferInstance
  exact commonChosenLoopLiftSquare.fac_left

lemma commonChosenLoopDiagramFamily_target :
    commonChosenLoopDiagramFamily.{u} ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation Sp.{u} 1 1 =
      commonNativeLoopEndpoint := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation Sp.{u} 1 1)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteι (SimplicialNerve CommonObject.{u})) inferInstance
  exact commonChosenLoopLiftSquare.fac_right

/-- 全族の各頂点は選び直さず、同じ元の共通四角形を厳密回収する。 -/
lemma commonChosenLoopDiagramFamily_vertex (v : (SimplicialNerve CommonObject.{u}) _⦋0⦌) :
    commonChosenLoopDiagramFamily.app _ v = commonChosenLoopVertex v := by
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app
    commonChosenLoopDiagramFamily_vertices (Opposite.op ⦋0⦌)) v
  change commonChosenLoopDiagramFamily.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v 0) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (commonChosenLoopVertex v) 0 at h
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero] using h

/-- 図式頂点から取り出す実四角形全体も、構成済みの同じ四角形。 -/
lemma commonChosenLoopDiagramFamily_square_vertex
    (v : (SimplicialNerve CommonObject.{u}) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram (commonChosenLoopDiagramFamily.app _ v).val =
      (commonLoopSquare (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject v).val).square := by
  rw [commonChosenLoopDiagramFamily_vertex]
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagram_functorVertex _

/-- 共通図式解像の切断。底の BF 比較を全単体で厳密回収。 -/
def commonChosenLoopDiagramSection :
    SimplicialNerve CommonObject.{u} ⟶ commonLoopDiagramResolution :=
  pullback.lift commonChosenLoopDiagramFamily (𝟙 _) (by
    rw [Category.id_comp]
    exact commonChosenLoopDiagramFamily_target)

@[reassoc (attr := simp)]
lemma commonChosenLoopDiagramSection_projection :
    commonChosenLoopDiagramSection.{u} ≫ commonLoopDiagramProjection = 𝟙 _ :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
lemma commonChosenLoopDiagramSection_family :
    commonChosenLoopDiagramSection.{u} ≫ commonLoopDiagramFamily =
      commonChosenLoopDiagramFamily :=
  pullback.lift_fst _ _ _

/-- 同じ選択族の始点関手。共通 refined 関手との全 Hom 比較を残す。 -/
def commonChosenLoopSource : SimplicialNerve CommonObject.{u} ⟶ Sp.{u} :=
  commonChosenLoopDiagramFamily ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation Sp.{u} 0 0

/-- 始点関手の各頂点は同じ共通 BF 対象に厳密一致する。 -/
lemma commonChosenLoopSource_vertex (v : (SimplicialNerve CommonObject.{u}) _⦋0⦌) :
    commonChosenLoopSource.app _ v =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (commonRefinement (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject v).val) := by
  change (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation Sp.{u} 0 0).app _
    (commonChosenLoopDiagramFamily.app _ v) = _
  rw [commonChosenLoopDiagramFamily_vertex, commonChosenLoopVertex,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopSquare.diagramVertex_evaluation]
  exact commonLoopSquare_vertex _

/-- 図式始点と refined 関手は全頂点で一致する。全単体の等式とは区別する。 -/
lemma commonChosenLoopSource_refined_vertex (v : (SimplicialNerve CommonObject.{u}) _⦋0⦌) :
    commonChosenLoopSource.app _ v = (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap commonRefinedEnriched).app _ v := by
  have h : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap commonRefinedEnriched).app _ v =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (commonRefinement (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject v).val) := by
    calc
      _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap commonRefinedEnriched).app _
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject v)) :=
        congrArg (fun z ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap commonRefinedEnriched).app _ z)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object v).symm
      _ = _ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex _ _
  exact (commonChosenLoopSource_vertex v).trans h.symm

/-- 全頂点を指定した同じ族と元の nativeLoop 図式族の全関手比較。 -/
def commonChosenLoopDiagramNativeIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso commonChosenLoopDiagramFamily.{u}
      (commonNativeLoopEndpoint ≫ nativeLoopTargetEquivalence.inv) :=
  nativeLoopDiagramFamilyIso _ _ (by
    rw [Category.assoc, nativeLoopTargetEquivalence_inv_target, Category.comp_id]
    exact commonChosenLoopDiagramFamily_target)

/-- 選択族の始点と nativeLoop の全関手同型。refined 関手との同型ではない。 -/
def commonChosenLoopSourceNativeIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso commonChosenLoopSource.{u} (commonNativeLoopEndpoint ≫ nativeLoop) := by
  have e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp commonChosenLoopDiagramNativeIso (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation Sp.{u} 0 0)
  simpa only [commonChosenLoopSource, Category.assoc, nativeLoop] using e

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
