module

public import SerrePositivity.KST.Spectra.AdjointLoopRelativeFullCoherentComparison
public import SerrePositivity.KST.Spectra.SpectrumTailEquivalence

/-!
概要：左右因子を保つ共通始域上で、比較先となる元の native loop 図式と厳密終点を固定する。
方針：元の tail と loop 図式切断を前合成し、既存の実 delooping 比較で成分候補を得る。
規約：対象ごとの同型から全図式同型を結論しない。
使われ方：d3b② の全 Hom 自然性を検査する指定された比較先。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
local instance relativeNativeDiagramSpectrumCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 概要：比較する loop 図式の厳密な終点は元の対象の一段移動。
方針：元の Sp を回収する射影と nativeTail を合成する。
規約：置換対象で終点を置き換えない。
使われ方：指定した loop 図式族の底。 -/
def fullNativeLoopEndpoint : SimplicialNerve FullObject ⟶ Sp.{u} :=
  fullOriginalInfinityMap ≫ nativeTail

/-- 概要：同じ終点上の元の native loop 図式族。
方針：終点を元の指定切断へ合成する。
規約：nativeLoop が正本であることを保持する。
使われ方：補助 BF 置換との全図式比較の標的。 -/
def fullNativeLoopDiagramFamily : SimplicialNerve FullObject ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams Sp.{u} :=
  fullNativeLoopEndpoint ≫ nativeLoopTargetEquivalence.inv

/-- 概要：比較先の全 loop 図式は指定終点を厳密に保つ。
方針：元の切断の厳密終点保存を前合成する。
規約：終点の同型で厳密等式を代用しない。
使われ方：指定境界を保つ全図式比較。 -/
lemma fullNativeLoopDiagramFamily_target :
    fullNativeLoopDiagramFamily.{u} ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation Sp.{u} 1 1 =
      fullNativeLoopEndpoint := by
  rw [fullNativeLoopDiagramFamily, Category.assoc,
    nativeLoopTargetEquivalence_inv_target, Category.comp_id]

/-- 概要：同じ全図式の始点は元の nativeLoop の前合成そのもの。
方針：元の nativeLoop の定義だけを開く。
規約：別の loop 関手を定義して同一視しない。
使われ方：②で必要な全図式同型の右端。 -/
lemma fullNativeLoopDiagramFamily_source :
    fullNativeLoopDiagramFamily.{u} ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation Sp.{u} 0 0 =
      fullNativeLoopEndpoint ≫ nativeLoop := by
  rw [fullNativeLoopDiagramFamily, Category.assoc]
  rfl

/-- 概要：指定終点の頂点は元の対象の実 tail 頂点。
方針：元の豊穣射影と nativeTail の頂点式を使う。
規約：元の対象を回収する。
使われ方：既存の点ごとの実 delooping 比較の適用。 -/
lemma fullNativeLoopEndpoint_vertex (X : FullObject.{u}) :
    fullNativeLoopEndpoint.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (tail X.val) := by
  change nativeTail.app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap fullOriginalEnriched).app _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex]
  exact nativeTail_vertex X.val

/-- 概要：指定した native loop の頂点から元の相対 BF 置換への成分候補。
方針：既存の実 delooping の頂点同型に、元の包含の同じ可逆辺を合成する。
規約：この成分候補の全 Hom 自然性は別途証明が必要。
使われ方：②の点ごとの π 同型と厳密自然性を区別する。 -/
def fullNativeLoopComponent (X : FullObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((fullNativeLoopEndpoint ≫ nativeLoop).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap fullReplacedEnriched).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X)) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (nativeLoop.app _
    (fullNativeLoopEndpoint.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X))) _
  rw [fullNativeLoopEndpoint_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex]
  haveI := isInvertible_of_piIsomorphism (inclusion X.val)
    (piIsomorphism_of_levelwise _ (inclusion_levelwise X.val))
  exact nativeLoopTailVertexIso X.val ≪≫
    asIso (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (inclusion X.val)))

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
