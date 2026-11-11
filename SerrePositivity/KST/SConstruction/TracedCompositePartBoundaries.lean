module
public import SerrePositivity.KST.SConstruction.PointedFixedVertexComposition
public import SerrePositivity.KST.SConstruction.TracedUnaryConstantPointData
public import SerrePositivity.KST.SConstruction.TracedCompositePointData
public import SerrePositivity.KST.SConstruction.TracedBFTriplePairStageTriangles

/-! # 元の合成補正の二部分の同じ全端点
概要：前の補正の後合成と後の補正の BF 前合成を、元の同じ合成補正の端点へ照合する。
方針：元の段射の関手法則・全族の評価・直通列制限の厳密な式を使う。
規約：共有中間族と両端族は全写像として同一であり、成分の一致で代用しない。
使われ方：元の二単一射補正の全木を一本の元の合成補正へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra Spectra.PointedMapping
open SerrePositivity.InfinityCategories
open scoped Simplicial
local instance compositePartPointedSimplicialCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y)

/-- 元の BF 境界の段評価は、同じ段頂点の定数零単体族。 -/
lemma monicKPrismTracedBFBoundary_stage_const (n : ℕ) :
    monicKPrismTracedBFBoundary F f ≫
        OmegaSpectrum.evaluation (kOmegaSpectrum (F.obj x)) (kOmegaSpectrum (F.obj y)) n =
      SSet.const (monicKTracedBFStageVertex F f n) := by
  rw [← SSet.yonedaEquiv_symm_zero]
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply, SSet.yonedaEquiv_comp, ← monicKTracedSpectrumMap_vertex]
  rfl

variable {z : I} (g : y ⟶ z)

/-- 前の補正を後合成した始点は、元の合成射の同じ raw 段頂点。 -/
lemma monicKPrismCompositePart_source (n : ℕ) :
    SSet.const (X := (Δ[0] : SSet.{u}))
        (familyVertex (monicKToRawLevelMap (F.map (f ≫ g)) n)) =
      SSet.const (familyVertex (monicKToRawLevelMap (F.map f) n)) ≫
        (PointedObject.basedHomMap ((kOmegaSpectrum (F.obj x)).level n).space
          (kKanSequenceLevelMap (F.map g) n)).right := by
  rw [SSet.const_comp]
  have hm : monicKToRawLevelMap (F.map (f ≫ g)) n =
      monicKToRawLevelMap (F.map f) n ≫ kKanSequenceLevelMap (F.map g) n := by
    rw [F.map_comp]
    simp only [monicKToRawLevelMap, kKanSequenceLevelMap_comp, Category.assoc]
  exact congrArg SSet.const ((congrArg familyVertex hm).trans
    (familyVertex_post (monicKToRawLevelMap (F.map f) n)
      (kKanSequenceLevelMap (F.map g) n)).symm)

/-- 前後二本の元の補正の共有中間族は、全零単体族として厳密に一致する。 -/
lemma monicKPrismCompositePart_middle (n : ℕ) :
    SSet.const (X := (Δ[0] : SSet.{u})) (monicKTracedRawStageVertex F f n) ≫
        (PointedObject.basedHomMap ((kOmegaSpectrum (F.obj x)).level n).space
          (kKanSequenceLevelMap (F.map g) n)).right =
      SSet.const (familyVertex (monicKToRawLevelMap (F.map g) n)) ≫
        monicKTracedTripleLastPairStageMap F f z n := by
  have hp : SSet.const (X := (Δ[0] : SSet.{u})) (monicKTracedRawStageVertex F f n) =
      SSet.const (monicKTracedBFStageVertex F f n) ≫
        (PointedObject.basedHomMap ((kOmegaSpectrum (F.obj x)).level n).space
          ((monicKKanSequenceProjection (F.obj y)).app n)).right :=
    (SSet.const_comp _ _).symm
  calc
    _ = SSet.const (X := (Δ[0] : SSet.{u})) (monicKTracedBFStageVertex F f n) ≫
        (PointedObject.basedHomMap ((kOmegaSpectrum (F.obj x)).level n).space
          (monicKToRawLevelMap (F.map g) n)).right := by
      rw [hp]
      simp only [monicKToRawLevelMap, ← PointedEnrichment.whiskerLeft_eq,
        eHomWhiskerLeft_comp, Category.assoc]
    _ = _ := ((pointedFixedLeftVertexComposition_apply (monicKTracedBFStageVertex F f n)
      (SSet.const (X := (Δ[0] : SSet.{u}))
        (familyVertex (monicKToRawLevelMap (F.map g) n)))).trans
          (pointedFamilyComposition_const_right _ (monicKToRawLevelMap (F.map g) n))).symm

/-- 元の合成補正の同じ終点は、後の単一射の補正終点の同じ BF 前合成。 -/
lemma monicKPrismCompositePart_target (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (compositionStringDirect f g) ≫ compositionStringPair f g ≫
        monicKPrismTracedRawComposition F f g ≫
          RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z)) n =
      SSet.const (monicKTracedRawStageVertex F g n) ≫
        monicKTracedTripleLastPairStageMap F f z n := by
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (compositionStringDirect f g) ≫ compositionStringPair f g ≫
      fst (nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f)) (nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString g)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (coherentArrowStringDirect f) := by
    rw [compositionStringPair_first, compositionStringFirst_direct]
  have hq : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (compositionStringDirect f g) ≫ compositionStringPair f g ≫
      snd (nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f)) (nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString g)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (coherentArrowStringDirect g) := by
    rw [compositionStringPair_second, compositionStringSecond_direct]
  rw [monicKPrismTracedRawComposition_evaluation,
    monicKTracedTripleLastPairStageMap]
  simp only [← Category.assoc, comp_lift, SSet.comp_const, Category.comp_id]
  congr 1
  apply CartesianMonoidalCategory.hom_ext
  · simp only [lift_fst]
    have hf := (congrArg (· ≫ monicKPrismTracedBFFamily F f) hp).trans
      (monicKPrismTracedBFFamily_boundary F f)
    simpa only [Category.assoc] using
      (congrArg (· ≫ OmegaSpectrum.evaluation (kOmegaSpectrum (F.obj x))
        (kOmegaSpectrum (F.obj y)) n) hf).trans (monicKPrismTracedBFBoundary_stage_const F f n)
  · simp only [lift_snd, Category.assoc, monicKPrismTracedRawFamily_evaluation]
    simpa only [Category.assoc] using
      (congrArg (· ≫ (monicKPrismTracedStage F g n).val) hq).trans
        (monicKPrismTracedStage_point_const F g n)

end SerrePositivity.KST.SConstruction
