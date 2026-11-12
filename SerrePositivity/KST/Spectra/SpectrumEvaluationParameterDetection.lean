module

public import SerrePositivity.KST.Spectra.SpectrumCotensorParameterNaturality
public import SerrePositivity.KST.Spectra.CotensorRestriction
public import SerrePositivity.KST.Spectra.RawSpectrumPreWhitehead
public import SerrePositivity.KST.Spectra.PostMappingIsomorphism

/-!
概要：元の評価写像の π 同型性は、パラメータの anodyne 置換の前後で同値。
方針：元の厳密な自然性正方形と、内部 Hom・BF 前合成の Whitehead 性を使う。
規約：全 Hom の射を比較する。使われ方：Kan 円評価から通常の円評価への移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.CotensorCompatible
open RawSpectrumMapping

local instance parameterDetectionHomKan (K : PointedSimplicialSet.{u})
    (X Y : OmegaSpectrum.{u}) :
    KanComplex ((ihom K).obj (RawSpectrumMapping.pointedSpace X Y.toKanSequence)).right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _

/-- パラメータの anodyne 射に沿い、元の評価自身の全基点 π 同型性を双方向に移す。 -/
lemma evaluationPost_piIsomorphism_iff_of_anodyne {A B : PointedSimplicialSet.{u}}
    (i : A ⟶ B) (hi : anodyneExtensions i.right) (X Y : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (evaluationPost A X Y).right ↔
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (evaluationPost B X Y).right := by
  have hp := pointedPre_piIsomorphism_of_levelwise (cotensorPre i X)
    (cotensorPre_levelwise_of_anodyne i hi X) Y.toKanSequence
  have hpost : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism
      ((ihom A).map (pointedPre (cotensorPre i X) Y.toKanSequence)).right :=
    PointedMapping.post_piIsomorphism A (pointedPre (cotensorPre i X) Y.toKanSequence) hp
  have hpre := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight _
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.anodyne_prePointed_rlp i hi
      (RawSpectrumMapping.pointedSpace (cotensor B X) Y.toKanSequence))
  have hc := congrArg Under.Hom.right (evaluationPost_parameter i X Y)
  rw [Under.comp_right, Under.comp_right] at hc
  constructor
  · intro h
    have hcomp := h.comp hpost
    rw [hc] at hcomp
    exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.of_comp hcomp hpre
  · intro h
    have hcomp := h.comp hpre
    rw [← hc] at hcomp
    exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.of_comp hcomp hpost

end SerrePositivity.KST.Spectra.OmegaSpectrum.CotensorCompatible
