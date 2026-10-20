module
public import SerrePositivity.KST.SConstruction.TracedBFWhiskerRawEvaluation
public import SerrePositivity.KST.SConstruction.PointedFamilyConstantComposition

/-! # 補正前の実交換辺と前二射 raw 段比較の後合成
概要：交換面の補正前の辺を、前二射の同じ raw 段比較辺の最終射による後合成へ同定する。
方針：元の BF 段辺の raw 射影と、元の段射による全 Hom 後合成の結合律を使う。
規約：元の同じ全一単体を保持し、端点や合成類だけの一致にしない。
使われ方：前二射の元の段三角形を、同じ実交換面へ厳密に貼る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra
open scoped Simplicial
local instance postBoundaryPointedSimplicialCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {w x y z : I} (f : w ⟶ x) (g : x ⟶ y) (h : y ⟶ z)

/-- 元の BF 段辺の raw 射影は、元の同じ raw 段比較辺全体。 -/
lemma monicKTracedCompositionBFLevelEdge_raw (n : ℕ) :
    SSet.yonedaEquiv.symm (monicKTracedCompositionBFLevelEdge F f g n).edge ≫
        (PointedObject.basedHomMap ((kOmegaSpectrum (F.obj w)).level n).space
          ((monicKKanSequenceProjection (F.obj y)).app n)).right =
      SSet.yonedaEquiv.symm (monicKTracedCompositionRawStageEdge F f g n).edge := by
  calc
    _ = (SSet.yonedaEquiv.symm (monicKTracedSpectrumCompositionEdge F f g).edge ≫
        OmegaSpectrum.evaluation (kOmegaSpectrum (F.obj w)) (kOmegaSpectrum (F.obj y)) n) ≫
          (PointedObject.basedHomMap ((kOmegaSpectrum (F.obj w)).level n).space
            ((monicKKanSequenceProjection (F.obj y)).app n)).right :=
      congrArg (· ≫ (PointedObject.basedHomMap ((kOmegaSpectrum (F.obj w)).level n).space
        ((monicKKanSequenceProjection (F.obj y)).app n)).right)
          (monicKTracedCompositionBFLevelEdge_map F f g n)
    _ = SSet.yonedaEquiv.symm (monicKTracedSpectrumCompositionEdge F f g).edge ≫
        kRawMappingProjection (F.obj w) (F.obj y) ≫
          RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj w)) (kKanSequence (F.obj y)) n := by
      rw [kRawMappingProjection_evaluation, Category.assoc]
    _ = _ := (monicKTracedCompositionRawStageEdge_map F f g n).symm

/-- 交換面の補正前の全辺は、元の前二射 raw 段辺を同じ最終段射で後合成した辺。 -/
lemma monicKTracedTripleInterchangeSecondLower_post (n : ℕ) :
    SSet.yonedaEquiv.symm (monicKTracedTripleInterchangeSecondLower F f g h n).edge =
      SSet.yonedaEquiv.symm (monicKTracedCompositionRawStageEdge F f g n).edge ≫
        (PointedObject.basedHomMap ((kOmegaSpectrum (F.obj w)).level n).space
          (kKanSequenceLevelMap (F.map h) n)).right := by
  rw [monicKTracedTripleInterchangeSecondLower_map, pointedFamilyComposition_const_right]
  calc
    _ = (SSet.yonedaEquiv.symm (monicKTracedCompositionBFLevelEdge F f g n).edge ≫
        (PointedObject.basedHomMap ((kOmegaSpectrum (F.obj w)).level n).space
          ((monicKKanSequenceProjection (F.obj y)).app n)).right) ≫
        (PointedObject.basedHomMap ((kOmegaSpectrum (F.obj w)).level n).space
          (kKanSequenceLevelMap (F.map h) n)).right := by
      simp only [monicKToRawLevelMap, ← PointedEnrichment.whiskerLeft_eq,
        eHomWhiskerLeft_comp, Category.assoc]
    _ = _ := congrArg (· ≫
      (PointedObject.basedHomMap ((kOmegaSpectrum (F.obj w)).level n).space
        (kKanSequenceLevelMap (F.map h) n)).right)
          (monicKTracedCompositionBFLevelEdge_raw F f g n)

end SerrePositivity.KST.SConstruction
