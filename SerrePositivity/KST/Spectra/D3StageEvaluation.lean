module

public import SerrePositivity.KST.Spectra.D3CommonProjectionNaturality
public import SerrePositivity.KST.SConstruction.PointedKanEnrichedEquivalences

/-!
概要：BF の全 Hom 段評価を、点つき Kan 複体への実豊穣関手として保持する。
方針：元の評価の単位・合成則と、元の Raw 前後合成の座標を使う。
規約：coherent な辺を元の段射と照合する。nativeLoop との同一視は含めない。
使われ方：共通 BF 右射影の全 Hom 自然性を各段の関手同型へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
local instance d3StageSpectrumCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance d3StagePointedCategory : SimplicialCategory PointedSimplicialSet.{u} :=
  PointedEnrichment.simplicialCategory

/-- Kan 値の元の豊穣関手を、同じ対象・全 Hom のまま全部分圏へ束ねる。 -/
def d3KanEnrichedLift {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    (F : EnrichedFunctor SSet.{u} C PointedSimplicialSet.{u})
    (hF : ∀ X, KanComplex (F.obj X).right) :
    EnrichedFunctor SSet.{u} C PointedKanObject.{u} where
  obj X := ⟨F.obj X, hF X⟩
  map X Y := F.map X Y
  map_id X := F.map_id X
  map_comp X Y Z := F.map_comp X Y Z

/-- 元の BF 対象と全 Hom を同じ段の点つき Kan 複体へ評価する。 -/
def d3StageKanEnriched (n : ℕ) :
    EnrichedFunctor SSet.{u} OmegaSpectrum.{u} PointedKanObject.{u} where
  obj X := ⟨(X.level n).space, (X.level n).kan⟩
  map X Y := evaluation X Y n
  map_id X := mappingIdentity_evaluation X n
  map_comp X Y Z := by
    change mappingComposition X Y Z ≫ evaluation X Z n = _
    rw [mappingComposition_evaluation]
    rfl

/-- 通常射の段評価と全 Hom 後合成の厳密な交換。 -/
@[reassoc]
lemma d3Stage_post {X Y Z : OmegaSpectrum.{u}} (f : Y ⟶ Z) (n : ℕ) :
    eHomWhiskerLeft SSet X f ≫ evaluation X Z n =
      evaluation X Y n ≫ eHomWhiskerLeft SSet (X.level n).space (f.app n) := by
  let q : KanSequence.Hom Y.toKanSequence Z.toKanSequence := ⟨f.app, f.comm⟩
  have h := RawSpectrumMapping.post_evaluation X q n
  dsimp only [q] at h
  rw [commonPost_spectrum] at h
  rw [PointedEnrichment.whiskerLeft_eq]
  exact h

/-- 通常射の段評価と全 Hom 前合成の厳密な交換。 -/
@[reassoc]
lemma d3Stage_pre {X Y Z : OmegaSpectrum.{u}} (f : X ⟶ Y) (n : ℕ) :
    eHomWhiskerRight SSet f Z ≫ evaluation X Z n =
      evaluation Y Z n ≫ eHomWhiskerRight SSet (f.app n) (Z.level n).space := by
  have h := RawSpectrumMapping.pre_evaluation f Z.toKanSequence n
  rw [RawSpectrumMapping.pre_spectrum] at h
  rw [PointedEnrichment.whiskerRight_eq]
  exact h

/-- 段評価を豊穣頂点に適用しても、元の段射そのものを回収する。 -/
lemma d3Stage_vertex {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (n : ℕ) :
    eHomEquiv SSet f ≫ (d3StageKanEnriched n).map X Y =
      eHomEquiv SSet (ObjectProperty.homMk (f.app n) :
        (d3StageKanEnriched n).obj X ⟶ (d3StageKanEnriched n).obj Y) := by
  have hf : eHomEquiv SSet f = vertexOfHomMap f := by
    change (SSet.unitHomEquiv _).symm ((SSet.unitHomEquiv _) (vertexOfHomMap f)) = _
    exact Equiv.symm_apply_apply _ _
  rw [hf]
  change vertexOfHomMap f ≫ evaluation X Y n = _
  rw [vertexOfHomMap_evaluation]
  rfl

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
