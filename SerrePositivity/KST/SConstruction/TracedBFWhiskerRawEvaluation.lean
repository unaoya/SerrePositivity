module
public import SerrePositivity.KST.SConstruction.PointedCompositionProjection
public import SerrePositivity.KST.SConstruction.TracedBFTripleInterchangeBoundary
public import SerrePositivity.KST.SConstruction.TracedBFWhiskerZeroEvaluation

/-! # 元の両 BF whisker の全 raw 段評価
概要：元の両 BF whisker の全区間を、固定段頂点と元の段比較辺の豊穣合成へ照合する。
方針：全 Hom の固定因子合成と段射影の式を、元の同じ BF 比較辺へ制限する。
規約：元の全一単体を保持し、定数な零段だけの主張にはしない。
使われ方：三入力の実交換面と四つの二入力段三角形の境界を厳密に貼る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra
open scoped Simplicial
local instance whiskerRawPointedSimplicialCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory
local instance whiskerRawSpectrumSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {w x y z : I} (f : w ⟶ x) (g : x ⟶ y) (h : y ⟶ z)

/-- 元の第二 BF whisker の全 raw 段評価は、元の前二射段辺と補正後の同じ終端の合成。 -/
lemma monicKTracedNativeSecondWhisker_raw_evaluation (n : ℕ) :
    SSet.yonedaEquiv.symm (monicKTracedNativeSecondWhisker F f g h).edge ≫
        kRawMappingProjection (F.obj w) (F.obj z) ≫
          RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj w)) (kKanSequence (F.obj z)) n =
      lift (SSet.yonedaEquiv.symm (monicKTracedCompositionBFLevelEdge F f g n).edge)
        (SSet.const (monicKTracedRawStageVertex F h n)) ≫
          eComp SSet ((kOmegaSpectrum (F.obj w)).level n).space
            ((kOmegaSpectrum (F.obj y)).level n).space
            ((kKanSequence (F.obj z)).level n).space := by
  rw [monicKTracedNativeSecondWhisker, enrichedComparisonRightWhisker_map]
  simp only [Category.assoc]
  rw [kRawMappingProjection_evaluation, spectrumFixedRightComposition_post_evaluation]
  simp only [← Category.assoc, comp_lift, Category.comp_id, SSet.comp_const, SSet.const_comp]
  exact congrArg (fun q => (lift q (SSet.const (monicKTracedRawStageVertex F h n)) ≫
    eComp SSet ((kOmegaSpectrum (F.obj w)).level n).space
      ((kOmegaSpectrum (F.obj y)).level n).space
      ((kKanSequence (F.obj z)).level n).space :
        (Δ[1] : SSet.{u}) ⟶ (PointedObject.basedHom
          ((kOmegaSpectrum (F.obj w)).level n).space
          ((kKanSequence (F.obj z)).level n).space).right))
    (monicKTracedCompositionBFLevelEdge_map F f g n).symm

/-- 元の第一 BF whisker の全 raw 段評価は、第一段射と後二射の元の raw 段辺の合成。 -/
lemma monicKTracedNativeFirstWhisker_raw_evaluation (n : ℕ) :
    SSet.yonedaEquiv.symm (monicKTracedNativeFirstWhisker F f g h).edge ≫
        kRawMappingProjection (F.obj w) (F.obj z) ≫
          RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj w)) (kKanSequence (F.obj z)) n =
      lift (SSet.const (monicKTracedBFStageVertex F f n))
        (SSet.yonedaEquiv.symm (monicKTracedCompositionRawStageEdge F g h n).edge) ≫
          eComp SSet ((kOmegaSpectrum (F.obj w)).level n).space
            ((kOmegaSpectrum (F.obj x)).level n).space
            ((kKanSequence (F.obj z)).level n).space := by
  rw [monicKTracedNativeFirstWhisker, enrichedComparisonLeftWhisker_map]
  simp only [Category.assoc]
  rw [kRawMappingProjection_evaluation, spectrumFixedLeftComposition_post_evaluation]
  simp only [← Category.assoc, comp_lift, SSet.comp_const]
  have he := monicKTracedCompositionRawStageEdge_map F g h n
  rw [kRawMappingProjection_evaluation] at he
  simp only [← Category.assoc] at he
  exact congrArg (fun q => (lift (SSet.const (monicKTracedBFStageVertex F f n)) q ≫
      eComp SSet ((kOmegaSpectrum (F.obj w)).level n).space
        ((kOmegaSpectrum (F.obj x)).level n).space
        ((kKanSequence (F.obj z)).level n).space :
          (Δ[1] : SSet.{u}) ⟶ (PointedObject.basedHom
            ((kOmegaSpectrum (F.obj w)).level n).space
            ((kKanSequence (F.obj z)).level n).space).right)) he.symm

/-- 元の実交換三角形対の第一上辺は、元の第二 BF whisker の全 raw 段評価そのもの。 -/
lemma monicKTracedTripleInterchangeFirstUpper_whisker (n : ℕ) :
    SSet.yonedaEquiv.symm (monicKTracedTripleInterchangeFirstUpper F f g h n).edge =
      SSet.yonedaEquiv.symm (monicKTracedNativeSecondWhisker F f g h).edge ≫
        kRawMappingProjection (F.obj w) (F.obj z) ≫
          RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj w)) (kKanSequence (F.obj z)) n :=
  (monicKTracedTripleInterchangeFirstUpper_map F f g h n).trans
    (monicKTracedNativeSecondWhisker_raw_evaluation F f g h n).symm

end SerrePositivity.KST.SConstruction
