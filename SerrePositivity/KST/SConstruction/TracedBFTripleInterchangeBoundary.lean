module
public import SerrePositivity.KST.SConstruction.TracedBFTripleInterchangePointSquare
public import SerrePositivity.KST.SConstruction.CartesianInterchangeEdgeMaps
public import SerrePositivity.KST.SConstruction.TracedBFStageVertices

/-! # 元の実交換三角形対の四つの全 raw 辺
概要：元の交換三角形対の全四辺を、元の補正全区間・BF 段辺・固定段頂点へ照合する。
方針：直積辺の全写像式を正しい合成順に移し、補正終点の同じ raw 段頂点を使う。
規約：同じ全一単体の等式を与え、合成類の式だけに帰着しない。
使われ方：左右三入力辺路の貼り合わせに用いる元の全交換境界。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra
open SerrePositivity.InfinityCategories Spectra.PointedMapping
open scoped Simplicial
local instance interchangeBoundaryPointedSimplicialCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory
local instance interchangeBoundarySpectrumSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {w x y z : I} (f : w ⟶ x) (g : x ⟶ y) (h : y ⟶ z)

/-- 第一経路下辺は、合成入力の BF 段射と最終射の元の全補正の同じ合成。 -/
lemma monicKTracedTripleInterchangeFirstLower_map (n : ℕ) :
    SSet.yonedaEquiv.symm (monicKTracedTripleInterchangeFirstLower F f g h n).edge =
      lift (SSet.const (monicKTracedBFStageVertex F (f ≫ g) n))
        (monicKTracedUnaryCorrectionAtPoint F h n) ≫
          eComp SSet ((kOmegaSpectrum (F.obj w)).level n).space
            ((kOmegaSpectrum (F.obj y)).level n).space
            ((kKanSequence (F.obj z)).level n).space := by
  rw [monicKTracedTripleInterchangeFirstLower, cartesianInterchangeFirstLower_map]
  rw [kStageRawReverseComposition, pointedReverseComposition_lift,
    monicKTracedUnaryCorrectionPointEdge_map]
  rfl

/-- 第一経路上辺は、元の BF 段比較辺と最終射の同じ補正後 raw 頂点の合成。 -/
lemma monicKTracedTripleInterchangeFirstUpper_map (n : ℕ) :
    SSet.yonedaEquiv.symm (monicKTracedTripleInterchangeFirstUpper F f g h n).edge =
      lift (SSet.yonedaEquiv.symm (monicKTracedCompositionBFLevelEdge F f g n).edge)
        (SSet.const (monicKTracedRawStageVertex F h n)) ≫
          eComp SSet ((kOmegaSpectrum (F.obj w)).level n).space
            ((kOmegaSpectrum (F.obj y)).level n).space
            ((kKanSequence (F.obj z)).level n).space := by
  rw [monicKTracedTripleInterchangeFirstUpper, cartesianInterchangeFirstUpper_map,
    kStageRawReverseComposition, pointedReverseComposition_lift]
  change lift _ (SSet.const (SSet.yonedaEquiv
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (coherentArrowStringDirect h) ≫ (monicKPrismTracedStage F h n).val))) ≫ _ = _
  rw [monicKPrismTracedStage_point_vertex]

/-- 第二経路下辺は、元の BF 段比較辺を最終射の補正前 raw 段射と合成した全区間。 -/
lemma monicKTracedTripleInterchangeSecondLower_map (n : ℕ) :
    SSet.yonedaEquiv.symm (monicKTracedTripleInterchangeSecondLower F f g h n).edge =
      lift (SSet.yonedaEquiv.symm (monicKTracedCompositionBFLevelEdge F f g n).edge)
        (SSet.const (familyVertex (monicKToRawLevelMap (F.map h) n))) ≫
          eComp SSet ((kOmegaSpectrum (F.obj w)).level n).space
            ((kOmegaSpectrum (F.obj y)).level n).space
            ((kKanSequence (F.obj z)).level n).space := by
  rw [monicKTracedTripleInterchangeSecondLower, cartesianInterchangeSecondLower_map,
    kStageRawReverseComposition, pointedReverseComposition_lift]
  change lift _ (SSet.const (SSet.yonedaEquiv
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (coherentArrowStringDirect h) ≫ monicKPrismRawLevelFamily n F h))) ≫ _ = _
  rw [monicKPrismRawLevelFamily, SSet.comp_const, ← SSet.yonedaEquiv_symm_zero,
    Equiv.apply_symm_apply]

/-- 第二経路上辺は、元の前二 BF 射の段合成と最終射の元の全補正の同じ合成。 -/
lemma monicKTracedTripleInterchangeSecondUpper_map (n : ℕ) :
    SSet.yonedaEquiv.symm (monicKTracedTripleInterchangeSecondUpper F f g h n).edge =
      lift (SSet.const
        ((OmegaSpectrum.evaluation (kOmegaSpectrum (F.obj w)) (kOmegaSpectrum (F.obj y)) n).app
          (Opposite.op ⦋0⦌) (SimplicialCategory.homEquiv' _ _
            (monicKTracedSpectrumMap F f ≫ monicKTracedSpectrumMap F g))))
        (monicKTracedUnaryCorrectionAtPoint F h n) ≫
          eComp SSet ((kOmegaSpectrum (F.obj w)).level n).space
            ((kOmegaSpectrum (F.obj y)).level n).space
            ((kKanSequence (F.obj z)).level n).space := by
  rw [monicKTracedTripleInterchangeSecondUpper, cartesianInterchangeSecondUpper_map,
    kStageRawReverseComposition, pointedReverseComposition_lift,
    monicKTracedUnaryCorrectionPointEdge_map]

end SerrePositivity.KST.SConstruction
