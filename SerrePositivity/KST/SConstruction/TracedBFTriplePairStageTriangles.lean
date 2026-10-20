module
public import SerrePositivity.KST.SConstruction.TracedBFTripleInterchangePostBoundary

/-! # 三入力の固定因子へ写した元の二つの全段三角形
概要：元の前二射・後二射の全段三角形を、固定因子の合成で同じ三入力 raw 空間へ写す。
方針：元の全二単体を実後合成し、全上辺を交換面・BF whisker と厳密に照合する。
規約：元の両全三角形と両補正辺を保持し、三角形を充填し直さない。
使われ方：三入力の四面と交換面を同じ全境界で貼り合わせる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra
open scoped Simplicial
local instance pairStagePointedSimplicialCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {w x y z : I} (f : w ⟶ x) (g : x ⟶ y) (h : y ⟶ z)

/-- 後二射の全段三角形を、元の第一 BF 段射と合成する同じ全 Hom 写像。 -/
def monicKTracedTripleLastPairStageMap (target : I) (n : ℕ) :
    (PointedObject.basedHom ((kOmegaSpectrum (F.obj x)).level n).space
      ((kKanSequence (F.obj target)).level n).space).right ⟶
    (PointedObject.basedHom ((kOmegaSpectrum (F.obj w)).level n).space
      ((kKanSequence (F.obj target)).level n).space).right :=
  lift (SSet.const (monicKTracedBFStageVertex F f n)) (𝟙 _) ≫
    eComp SSet ((kOmegaSpectrum (F.obj w)).level n).space
      ((kOmegaSpectrum (F.obj x)).level n).space ((kKanSequence (F.obj target)).level n).space

/-- 元の前二射の全段三角形を、元の同じ最終段射で後合成した実三角形。 -/
def monicKTracedTripleFirstPairStageTriangle (n : ℕ) :=
  (monicKTracedCompositionStageTriangleData F f g n).triangle.map
    (PointedObject.basedHomMap ((kOmegaSpectrum (F.obj w)).level n).space
      (kKanSequenceLevelMap (F.map h) n)).right

/-- 元の後二射の全段三角形を、元の同じ第一 BF 段射と合成した実三角形。 -/
def monicKTracedTripleLastPairStageTriangle (n : ℕ) :=
  (monicKTracedCompositionStageTriangleData F g h n).triangle.map
    (monicKTracedTripleLastPairStageMap F f z n)

/-- 前二射の全二単体は、元の同じ全 span の後合成像そのもの。 -/
lemma monicKTracedTripleFirstPairStageTriangle_realization (n : ℕ) :
    SSet.yonedaEquiv.symm (monicKTracedTripleFirstPairStageTriangle F f g h n).simplex =
      monicKTracedCompositionCorrectedSpan F f g n ≫
        (PointedObject.basedHomMap ((kOmegaSpectrum (F.obj w)).level n).space
          (kKanSequenceLevelMap (F.map h) n)).right :=
  (SSet.yonedaEquiv_symm_comp _ _).symm.trans
    (congrArg (· ≫ (PointedObject.basedHomMap ((kOmegaSpectrum (F.obj w)).level n).space
      (kKanSequenceLevelMap (F.map h) n)).right)
        (monicKTracedCompositionStageTriangleData_realization F f g n))

/-- 後二射の全二単体も、元の同じ全 span を第一段射と合成した像そのもの。 -/
lemma monicKTracedTripleLastPairStageTriangle_realization (n : ℕ) :
    SSet.yonedaEquiv.symm (monicKTracedTripleLastPairStageTriangle F f g h n).simplex =
      monicKTracedCompositionCorrectedSpan F g h n ≫
        monicKTracedTripleLastPairStageMap F f z n :=
  (SSet.yonedaEquiv_symm_comp
    (monicKTracedCompositionStageTriangleData F g h n).triangle.simplex
    (monicKTracedTripleLastPairStageMap F f z n)).symm.trans
    (congrArg (· ≫ monicKTracedTripleLastPairStageMap F f z n)
      (monicKTracedCompositionStageTriangleData_realization F g h n))

/-- 前二射三角形の上面全体は、元の実交換三角形対の補正前の全辺。 -/
lemma monicKTracedTripleFirstPairStageTriangle_upper (n : ℕ) :
    stdSimplex.δ 0 ≫
        SSet.yonedaEquiv.symm (monicKTracedTripleFirstPairStageTriangle F f g h n).simplex =
      SSet.yonedaEquiv.symm (monicKTracedTripleInterchangeSecondLower F f g h n).edge :=
  (SSet.Edge.CompStruct.δ_zero_yonedaEquiv_symm
    (monicKTracedTripleFirstPairStageTriangle F f g h n)).trans
      ((SSet.yonedaEquiv_symm_comp _ _).symm.trans
        (monicKTracedTripleInterchangeSecondLower_post F f g h n).symm)

/-- 後二射三角形の上面全体は、元の第一 BF whisker の同じ全 raw 段評価。 -/
lemma monicKTracedTripleLastPairStageTriangle_upper (n : ℕ) :
    stdSimplex.δ 0 ≫
        SSet.yonedaEquiv.symm (monicKTracedTripleLastPairStageTriangle F f g h n).simplex =
      SSet.yonedaEquiv.symm (monicKTracedNativeFirstWhisker F f g h).edge ≫
        kRawMappingProjection (F.obj w) (F.obj z) ≫
          RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj w)) (kKanSequence (F.obj z)) n := by
  rw [SSet.Edge.CompStruct.δ_zero_yonedaEquiv_symm, SSet.Edge.map_edge,
    ← SSet.yonedaEquiv_symm_comp, monicKTracedTripleLastPairStageMap]
  simp only [← Category.assoc, comp_lift, SSet.comp_const, Category.comp_id]
  exact (monicKTracedNativeFirstWhisker_raw_evaluation F f g h n).symm

/-- 前二射の元の第一補正辺全体も、同じ三角形の下面の同じ後合成像として保持する。 -/
lemma monicKTracedTripleFirstPairStageTriangle_first (n : ℕ) :
    stdSimplex.δ 2 ≫
        SSet.yonedaEquiv.symm (monicKTracedTripleFirstPairStageTriangle F f g h n).simplex =
      SSet.yonedaEquiv.symm (monicKTracedCompositionStageTriangleData F f g n).first.edge ≫
        (PointedObject.basedHomMap ((kOmegaSpectrum (F.obj w)).level n).space
          (kKanSequenceLevelMap (F.map h) n)).right :=
  (SSet.Edge.CompStruct.δ_two_yonedaEquiv_symm
    (monicKTracedTripleFirstPairStageTriangle F f g h n)).trans
      (SSet.yonedaEquiv_symm_comp _ _).symm

/-- 前二射の元の全合成補正辺も、同じ三角形の対角面として保持する。 -/
lemma monicKTracedTripleFirstPairStageTriangle_direct (n : ℕ) :
    stdSimplex.δ 1 ≫
        SSet.yonedaEquiv.symm (monicKTracedTripleFirstPairStageTriangle F f g h n).simplex =
      SSet.yonedaEquiv.symm (monicKTracedCompositionStageTriangleData F f g n).direct.edge ≫
        (PointedObject.basedHomMap ((kOmegaSpectrum (F.obj w)).level n).space
          (kKanSequenceLevelMap (F.map h) n)).right :=
  (SSet.Edge.CompStruct.δ_one_yonedaEquiv_symm
    (monicKTracedTripleFirstPairStageTriangle F f g h n)).trans
      (SSet.yonedaEquiv_symm_comp _ _).symm

/-- 後二射の元の第一補正辺全体も、同じ三角形の下面の同じ実合成像として保持する。 -/
lemma monicKTracedTripleLastPairStageTriangle_first (n : ℕ) :
    stdSimplex.δ 2 ≫
        SSet.yonedaEquiv.symm (monicKTracedTripleLastPairStageTriangle F f g h n).simplex =
      SSet.yonedaEquiv.symm (monicKTracedCompositionStageTriangleData F g h n).first.edge ≫
        monicKTracedTripleLastPairStageMap F f z n :=
  (SSet.Edge.CompStruct.δ_two_yonedaEquiv_symm
    (monicKTracedTripleLastPairStageTriangle F f g h n)).trans
      (SSet.yonedaEquiv_symm_comp
        (monicKTracedCompositionStageTriangleData F g h n).first.edge
        (monicKTracedTripleLastPairStageMap F f z n)).symm

/-- 後二射の元の全合成補正辺も、同じ三角形の対角面の同じ実合成像として保持する。 -/
lemma monicKTracedTripleLastPairStageTriangle_direct (n : ℕ) :
    stdSimplex.δ 1 ≫
        SSet.yonedaEquiv.symm (monicKTracedTripleLastPairStageTriangle F f g h n).simplex =
      SSet.yonedaEquiv.symm (monicKTracedCompositionStageTriangleData F g h n).direct.edge ≫
        monicKTracedTripleLastPairStageMap F f z n :=
  (SSet.Edge.CompStruct.δ_one_yonedaEquiv_symm
    (monicKTracedTripleLastPairStageTriangle F f g h n)).trans
      (SSet.yonedaEquiv_symm_comp
        (monicKTracedCompositionStageTriangleData F g h n).direct.edge
        (monicKTracedTripleLastPairStageMap F f z n)).symm

end SerrePositivity.KST.SConstruction
