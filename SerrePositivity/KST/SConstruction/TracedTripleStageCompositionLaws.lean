module
public import SerrePositivity.KST.SConstruction.SpectrumStageFixedComposition
public import SerrePositivity.KST.SConstruction.TracedTripleBinaryGlue

/-! # 三入力の元の段射による前後合成の厳密な法則
概要：元の BF 段射の前合成と元の raw 段射の後合成の交換・両結合則を回収する。
方針：元の全 Hom 合成を通常の点つき前合成へ写し、豊穣の前後合成則を適用する。
規約：同じ全写像の厳密等号であり、成分の法則で代用しない。
使われ方：左右の三本補正辺路の全共通辺を同定する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra
open scoped Simplicial
local instance tripleStagePointedSimplicialCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory
local instance tripleStageSpectrumSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {w x y z : I} (f : w ⟶ x) (g : x ⟶ y) (h : y ⟶ z)

/-- 元の固定 BF 段頂点の合成写像は、元の同じ点つき段射の前合成。 -/
lemma monicKTracedTripleLastPairStageMap_pre (target : I) (n : ℕ) :
    monicKTracedTripleLastPairStageMap F f target n =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((monicKTracedSpectrumMap F f).app n)
        ((kKanSequence (F.obj target)).level n).space :=
  spectrumStageFixedLeftComposition_pre (monicKTracedSpectrumMap F f) _ n

/-- 元の BF 第一段射の前合成は、元の raw 後続段射の後合成と厳密に可換。 -/
lemma monicKTracedTripleLastPairStageMap_post (n : ℕ) :
    monicKTracedTripleLastPairStageMap F f y n ≫
        (PointedObject.basedHomMap ((kOmegaSpectrum (F.obj w)).level n).space
          (kKanSequenceLevelMap (F.map h) n)).right =
      (PointedObject.basedHomMap ((kOmegaSpectrum (F.obj x)).level n).space
        (kKanSequenceLevelMap (F.map h) n)).right ≫
          monicKTracedTripleLastPairStageMap F f z n := by
  rw [monicKTracedTripleLastPairStageMap_pre, monicKTracedTripleLastPairStageMap_pre]
  simp only [← PointedEnrichment.whiskerRight_eq, ← PointedEnrichment.whiskerLeft_eq]
  exact (eHom_whisker_exchange SSet ((monicKTracedSpectrumMap F f).app n)
    (kKanSequenceLevelMap (F.map h) n)).symm

/-- 元の二 BF 段射の前合成を連ねると、同じ BF 合成頂点との全 Hom 合成。 -/
lemma monicKTracedTripleLastPairStageMap_comp (n : ℕ) :
    monicKTracedTripleLastPairStageMap F g z n ≫ monicKTracedTripleLastPairStageMap F f z n =
      lift (SSet.const
        ((OmegaSpectrum.evaluation (kOmegaSpectrum (F.obj w)) (kOmegaSpectrum (F.obj y)) n).app
          (Opposite.op ⦋0⦌) (SimplicialCategory.homEquiv' _ _
            (monicKTracedSpectrumMap F f ≫ monicKTracedSpectrumMap F g)))) (𝟙 _) ≫
          eComp SSet ((kOmegaSpectrum (F.obj w)).level n).space
            ((kOmegaSpectrum (F.obj y)).level n).space
            ((kKanSequence (F.obj z)).level n).space := by
  rw [monicKTracedTripleLastPairStageMap_pre, monicKTracedTripleLastPairStageMap_pre]
  calc
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre
        ((monicKTracedSpectrumMap F f ≫ monicKTracedSpectrumMap F g).app n)
          ((kKanSequence (F.obj z)).level n).space := by
      change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((monicKTracedSpectrumMap F g).app n) _ ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((monicKTracedSpectrumMap F f).app n) _ =
          _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre
            ((monicKTracedSpectrumMap F f).app n ≫ (monicKTracedSpectrumMap F g).app n) _
      rw [← PointedEnrichment.whiskerRight_eq, ← PointedEnrichment.whiskerRight_eq,
        ← PointedEnrichment.whiskerRight_eq, eHomWhiskerRight_comp]
    _ = _ := (spectrumStageFixedLeftComposition_pre
      (monicKTracedSpectrumMap F f ≫ monicKTracedSpectrumMap F g)
      ((kKanSequence (F.obj z)).level n).space n).symm

/-- 元の二 raw 後続段射の後合成は、元の合成入力の同じ全 Hom 後合成。 -/
lemma monicKTracedTripleRawPost_comp (n : ℕ) :
    (PointedObject.basedHomMap ((kOmegaSpectrum (F.obj w)).level n).space
        (kKanSequenceLevelMap (F.map g) n)).right ≫
      (PointedObject.basedHomMap ((kOmegaSpectrum (F.obj w)).level n).space
        (kKanSequenceLevelMap (F.map h) n)).right =
      (PointedObject.basedHomMap ((kOmegaSpectrum (F.obj w)).level n).space
        (kKanSequenceLevelMap (F.map (g ≫ h)) n)).right := by
  rw [F.map_comp, kKanSequenceLevelMap_comp]
  simp only [← PointedEnrichment.whiskerLeft_eq, eHomWhiskerLeft_comp]

end SerrePositivity.KST.SConstruction
