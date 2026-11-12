module

public import SerrePositivity.KST.Spectra.SpectrumCotensorPointedComparison
public import SerrePositivity.KST.Spectra.RawSpectrumCotensorSourceNaturality
public import SerrePositivity.KST.Spectra.SphereMappingComponents
public import SerrePositivity.KST.Spectra.SpectrumMappingComponents
public import SerrePositivity.KST.Spectra.KanEquivalenceBridge

/-!
概要：元の円 cotensor への BF 射の成分を、元の Hom の基本群で表示する。
方針：元の cotensor 比較の π₀ 同値と円の成分表示を合成し、源の前合成を追跡する。
規約：実際の BF 射と全 Hom を保持。使われ方：頂点の符号反転の構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance circleCotensorComponentsSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 元の cotensor 比較は、元の BF 射による源の前合成と厳密に可換。 -/
lemma cotensorPointedMappingComparison_pre_source {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y)
    (Z : OmegaSpectrum.{u}) (A : PointedSimplicialSet.{u}) :
    RawSpectrumMapping.pointedPre f (cotensor A Z).toKanSequence ≫
      cotensorPointedMappingComparison X Z A =
    cotensorPointedMappingComparison Y Z A ≫
      (ihom A).map (RawSpectrumMapping.pointedPre f Z.toKanSequence) := by
  unfold cotensorPointedMappingComparison
  rw [← Category.assoc, ← RawSpectrumMapping.pointedPre_post, Category.assoc,
    RawSpectrumMapping.cotensorComparison_pre_source, Category.assoc]

/-- 一般の列としての前合成は、BF 標的では元の豊穣前合成そのもの。 -/
lemma rawPointedPre_right {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (Z : OmegaSpectrum.{u}) :
    (RawSpectrumMapping.pointedPre f Z.toKanSequence).right =
      SpectrumMappingAcyclic.pre f Z := by
  change (λ_ (mappingSpace Y Z)).inv ≫ vertexOfHomMap f ▷ mappingSpace Y Z ≫
    RawSpectrumMapping.composition X Y Z.toKanSequence = _
  rw [RawSpectrumMapping.composition_spectrum]
  change _ = (λ_ (mappingSpace Y Z)).inv ≫
    (SSet.unitHomEquiv _).symm (vertexOfHom f) ▷ mappingSpace Y Z ≫ mappingComposition X Y Z
  rw [vertexOfHom, Equiv.symm_apply_apply]

/-- 元の円 cotensor への BF 射の成分を、元の Hom の基本群へ送る標準比較。 -/
def circleCotensorComponentClass (X Y : OmegaSpectrum.{u}) :
    π₀ (mappingSpace X (cotensor PointedSimplicialSet.circle Y)) →
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (RawSpectrumMapping.pointedSpace X Y.toKanSequence).right 0
        (RawSpectrumMapping.pointedSpace X Y.toKanSequence).basepoint :=
  SphereSimplex.componentClass (RawSpectrumMapping.pointedSpace X Y.toKanSequence) 0 ∘
    mapπ₀ (cotensorMappingEquivalence X Y PointedSimplicialSet.circle).hom

/-- 比較の全単射性は、元の cotensor の同値と元の円の成分表示から従う。 -/
lemma circleCotensorComponentClass_bijective (X Y : OmegaSpectrum.{u}) :
    Function.Bijective (circleCotensorComponentClass X Y) := by
  have h := kanPiIsomorphism_of_qCatEquivalence
    (cotensorMappingEquivalence X Y PointedSimplicialSet.circle).hom
    (cotensorMappingEquivalence X Y PointedSimplicialSet.circle).isQCatEquivalence
  exact (SphereSimplex.componentClass_bijective
    (RawSpectrumMapping.pointedSpace X Y.toKanSequence) 0).comp
      (h.piZero_bijective_at
        (RawSpectrumMapping.pointedSpace X
          (cotensor PointedSimplicialSet.circle Y).toKanSequence).basepoint)

/-- 元の BF 射の成分と、元の Hom の基本群との集合の同値。 -/
def circleCotensorComponentEquiv (X Y : OmegaSpectrum.{u}) :
    π₀ (mappingSpace X (cotensor PointedSimplicialSet.circle Y)) ≃
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (RawSpectrumMapping.pointedSpace X Y.toKanSequence).right 0
        (RawSpectrumMapping.pointedSpace X Y.toKanSequence).basepoint :=
  Equiv.ofBijective _ (circleCotensorComponentClass_bijective X Y)

/-- 元の比較は BF 源の前合成を、元の Hom の基本群の前合成へ厳密に送る。 -/
lemma circleCotensorComponentClass_pre {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y)
    (Z : OmegaSpectrum.{u})
    (a : π₀ (mappingSpace Y (cotensor PointedSimplicialSet.circle Z))) :
    circleCotensorComponentClass X Z
      (mapπ₀ (SpectrumMappingAcyclic.pre f (cotensor PointedSimplicialSet.circle Z)) a) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (RawSpectrumMapping.pointedPre f Z.toKanSequence).right
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (RawSpectrumMapping.pointedPre f Z.toKanSequence))
      (circleCotensorComponentClass Y Z a) := by
  have h := congrArg (fun q ↦ mapπ₀ q.right a)
    (cotensorPointedMappingComparison_pre_source f Z PointedSimplicialSet.circle)
  simp only [Under.comp_right, mapπ₀_comp_apply, rawPointedPre_right,
    cotensorPointedMappingComparison_right] at h
  unfold circleCotensorComponentClass
  dsimp only [Function.comp_apply]
  rw [h]
  exact SphereSimplex.componentClass_natural 0 _ _

end SerrePositivity.KST.Spectra.OmegaSpectrum
