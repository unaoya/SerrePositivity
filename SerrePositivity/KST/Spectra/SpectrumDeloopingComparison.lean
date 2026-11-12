module

public import SerrePositivity.KST.Spectra.SpectrumNativeLoopComparison
public import SerrePositivity.KST.Spectra.TailCotensorComparison
public import SerrePositivity.KST.Spectra.OriginalLoopModelMap

/-!
概要：各スペクトルを一段先の対象の実際の loop 四角形と比較する。
方針：既存の構造比較、一段移動と cotensor の比較、円の置換、native loop 比較を合成する。
規約：対象ごとの実際の同値を構成する。loop 関手の同値性や安定性は仮定しない。
使われ方：HA §1.4.2、Sp の delooping と安定性。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum

/-- 元の対象から一段先の対象の具体的な native loop への実際の BF 射。 -/
def deloopingComparison (X : OmegaSpectrum.{u}) : X ⟶ BasedLoop.obj (tail X) :=
  originalLoopModelMap X ≫ tailCotensorComparison CirclePower.space X ≫
    cotensorPre CirclePower.unit (tail X) ≫ BasedLoop.circleComparison (tail X)

/-- delooping 比較は各段で全基点 π 同型。 -/
lemma deloopingComparison_levelwise (X : OmegaSpectrum.{u}) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((deloopingComparison X).app n).right :=
  (originalLoopModelMap_levelwise X n).comp
    ((tailCotensorComparison_levelwise CirclePower.space X n).comp
      ((cotensorPre_levelwise_of_anodyne CirclePower.unit
        (PointedKanReplacement.unit_anodyne PointedSimplicialSet.circle) (tail X) n).comp
        (BasedLoop.circleComparison_levelwise (tail X) n)))

local instance deloopingSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance deloopingHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := OmegaSpectrum.mappingSpace_kanComplex X Y

/-- 指定した delooping 比較辺は元の Sp の同値。 -/
lemma deloopingComparison_isInvertible (X : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (deloopingComparison X)) :=
  SpectrumMappingAcyclic.isInvertible_of_levelwise _ (deloopingComparison_levelwise X)

/-- 元の対象と一段先の対象の実際の loop 四角形の頂点の同型。 -/
def deloopingVertexIso (X : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) (BasedLoop.square (tail X)).vertex := by
  rw [BasedLoop.square_vertex]
  haveI := deloopingComparison_isInvertible X
  exact asIso (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (deloopingComparison X)))

end SerrePositivity.KST.Spectra.OmegaSpectrum
