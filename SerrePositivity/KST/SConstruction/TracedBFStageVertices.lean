module
public import SerrePositivity.KST.SConstruction.TracedBFInterchangeInputs

/-! # 元の BF 段頂点と同じ raw 補正終点
概要：元の BF 境界の段評価と raw 射影を、元の補正終点の直通列評価へ照合する。
方針：元の全 BF 族の段評価と境界制限を、同じ米田頂点へ移す。
規約：既存の BF 射・全段補正・直通列点を変更しない。
使われ方：三入力の実交換辺を元の BF whisker の全 raw 段評価へ同定する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet Spectra
open SerrePositivity.InfinityCategories
open scoped Simplicial
local instance stageVertexSpectrumSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y)

/-- 元の BF 境界射の同じ段頂点。 -/
def monicKTracedBFStageVertex (n : ℕ) :=
  (OmegaSpectrum.evaluation (kOmegaSpectrum (F.obj x)) (kOmegaSpectrum (F.obj y)) n).app
    (Opposite.op ⦋0⦌) (SimplicialCategory.homEquiv' _ _ (monicKTracedSpectrumMap F f))

/-- 元の BF 段頂点の同じ raw 射影。 -/
def monicKTracedRawStageVertex (n : ℕ) :=
  ((PointedObject.basedHomMap ((kOmegaSpectrum (F.obj x)).level n).space
    ((monicKKanSequenceProjection (F.obj y)).app n)).right).app (Opposite.op ⦋0⦌)
      (monicKTracedBFStageVertex F f n)

/-- 元の補正済み段の直通列制限は、元の同じ BF 境界の段評価・raw 射影。 -/
lemma monicKPrismTracedStage_point (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (coherentArrowStringDirect f) ≫ (monicKPrismTracedStage F f n).val =
      monicKPrismTracedBFBoundary F f ≫
        OmegaSpectrum.evaluation (kOmegaSpectrum (F.obj x)) (kOmegaSpectrum (F.obj y)) n ≫
          (PointedObject.basedHomMap ((kOmegaSpectrum (F.obj x)).level n).space
            ((monicKKanSequenceProjection (F.obj y)).app n)).right := by
  have he := monicKPrismTracedBFFamily_evaluation F f n
  change monicKPrismTracedBFFamily F f ≫ _ ≫ _ = (monicKPrismTracedStage F f n).val at he
  rw [← he, ← Category.assoc, monicKPrismTracedBFFamily_boundary]

/-- 元の補正終点の頂点は、元の BF 射の同じ raw 段頂点。 -/
lemma monicKPrismTracedStage_point_vertex (n : ℕ) :
    SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (coherentArrowStringDirect f) ≫
      (monicKPrismTracedStage F f n).val) = monicKTracedRawStageVertex F f n := by
  rw [monicKPrismTracedStage_point, ← Category.assoc, SSet.yonedaEquiv_comp,
    SSet.yonedaEquiv_comp,
    ← monicKTracedSpectrumMap_vertex]
  rfl

end SerrePositivity.KST.SConstruction
