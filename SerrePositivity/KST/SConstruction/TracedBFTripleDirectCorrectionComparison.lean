module
public import SerrePositivity.KST.SConstruction.TracedBFDirectCorrectionNormalization
public import SerrePositivity.KST.SConstruction.TargetFixedBoundaryCospan

/-! # 三入力の左右結合で共有する元の直接補正の実比較
概要：左右の元の実三角形の直接補正辺を、同じ単一合成射の円柱を通して実比較する。
方針：結合則は終点円柱の表示だけに使い、元の両正規化円柱を固定境界空間で貼る。
規約：元の全両円柱を高次比較の面に保持する。全三入力の coherence 完了は主張しない。
使われ方：四つの実 BF 合成面の共有直接補正を厳密に合わせて消去する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra
open scoped Simplicial
local instance tripleDirectComparisonSpectrumSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {w x y z : I} (f : w ⟶ x) (g : x ⟶ y) (h : y ⟶ z)

/-- 元の左結合の正規化円柱を保持し、共通単一合成射の括弧表示だけを合わせる。 -/
def monicKTracedTripleDirectLeftNormalization (n : ℕ) :=
  familyHomotopyEndpointTransport (monicKTracedCompositionStageFirstNormalization F (f ≫ g) h n)
    rfl (congrArg (fun k => monicKTracedUnaryCorrectionAtPoint F k n) (Category.assoc f g h))

/-- 括弧の表示移送でも、元の同じ左結合の全正規化円柱を保持する。 -/
lemma monicKTracedTripleDirectLeftNormalization_h (n : ℕ) :
    (monicKTracedTripleDirectLeftNormalization F f g h n).h =
      (monicKTracedCompositionStageFirstNormalization F (f ≫ g) h n).h :=
  familyHomotopyEndpointTransport_h _ _ _

/-- 左結合の元の直接補正辺の全境界を、正規化の全時刻で厳密に固定する。 -/
lemma monicKTracedTripleDirectLeftNormalization_relative (n : ℕ) :
    ((SSet.boundary 1).ι ▷ (Δ[1] : SSet.{u})) ≫
        (monicKTracedTripleDirectLeftNormalization F f g h n).h =
      fst (∂Δ[1] : SSet.{u}) Δ[1] ≫ (SSet.boundary 1).ι ≫
        SSet.yonedaEquiv.symm
          (monicKTracedCompositionStageTriangleData F (f ≫ g) h n).first.edge := by
  rw [monicKTracedTripleDirectLeftNormalization_h]
  exact monicKTracedCompositionStageFirstNormalization_relative F (f ≫ g) h n

/-- 元の左右直接補正辺の全境界固定比較と、元の両正規化円柱を保持する実三角形。 -/
def monicKTracedTripleDirectComparisonData (n : ℕ) :=
  targetFixedBoundaryCospan (SSet.boundary 1).ι
    (monicKTracedTripleDirectLeftNormalization F f g h n)
    (monicKTracedCompositionStageFirstNormalization F f (g ≫ h) n)
    (monicKTracedTripleDirectLeftNormalization_relative F f g h n)
    (monicKTracedCompositionStageFirstNormalization_relative F f (g ≫ h) n)

/-- 元の左右実三角形の共有直接補正辺を結ぶ同じ全実比較円柱。 -/
def monicKTracedTripleDirectComparison (n : ℕ) :=
  (monicKTracedTripleDirectComparisonData F f g h n).homotopy

/-- 元の左結合三角形の直接補正辺全体を、比較の始端に厳密に保持する。 -/
lemma monicKTracedTripleDirectComparison_source (n : ℕ) :
    SSet.ι₀ ≫ (monicKTracedTripleDirectComparison F f g h n).h =
      SSet.yonedaEquiv.symm
        (monicKTracedCompositionStageTriangleData F (f ≫ g) h n).first.edge :=
  (monicKTracedTripleDirectComparison F f g h n).h₀

/-- 元の右結合三角形の直接補正辺全体も、比較の終端に厳密に保持する。 -/
lemma monicKTracedTripleDirectComparison_target (n : ℕ) :
    SSet.ι₁ ≫ (monicKTracedTripleDirectComparison F f g h n).h =
      SSet.yonedaEquiv.symm
        (monicKTracedCompositionStageTriangleData F f (g ≫ h) n).first.edge :=
  (monicKTracedTripleDirectComparison F f g h n).h₁

/-- 元の左右比較の全境界を全比較時刻で厳密に固定する。 -/
lemma monicKTracedTripleDirectComparison_relative (n : ℕ) :
    ((SSet.boundary 1).ι ▷ (Δ[1] : SSet.{u})) ≫
        (monicKTracedTripleDirectComparison F f g h n).h =
      fst (∂Δ[1] : SSet.{u}) Δ[1] ≫ (SSet.boundary 1).ι ≫
        monicKTracedUnaryCorrectionAtPoint F (f ≫ g ≫ h) n :=
  (monicKTracedTripleDirectComparisonData F f g h n).relative

/-- 元の左右実辺の全区間と両正規化円柱を面に持つ同じ実高次比較。 -/
def monicKTracedTripleDirectComparisonRealization (n : ℕ) :=
  familyCompStructRealization (monicKTracedTripleDirectComparisonData F f g h n).triangle

/-- 指定面は、左右の元の直接補正辺を結ぶ同じ全比較円柱。 -/
lemma monicKTracedTripleDirectComparisonRealization_comparison (n : ℕ) :
    ((Δ[1] : SSet.{u}) ◁ stdSimplex.δ 2) ≫
        monicKTracedTripleDirectComparisonRealization F f g h n =
      (monicKTracedTripleDirectComparison F f g h n).h :=
  familyCompStructRealization_first _

/-- 元の左正規化円柱全体を、高次比較の同じ合成面に厳密に保持する。 -/
lemma monicKTracedTripleDirectComparisonRealization_left (n : ℕ) :
    ((Δ[1] : SSet.{u}) ◁ stdSimplex.δ 1) ≫
        monicKTracedTripleDirectComparisonRealization F f g h n =
      (monicKTracedCompositionStageFirstNormalization F (f ≫ g) h n).h :=
  (familyCompStructRealization_direct _).trans
    (monicKTracedTripleDirectLeftNormalization_h F f g h n)

/-- 元の右正規化円柱全体も、高次比較の同じ第二面に厳密に保持する。 -/
lemma monicKTracedTripleDirectComparisonRealization_right (n : ℕ) :
    ((Δ[1] : SSet.{u}) ◁ stdSimplex.δ 0) ≫
        monicKTracedTripleDirectComparisonRealization F f g h n =
      (monicKTracedCompositionStageFirstNormalization F f (g ≫ h) n).h :=
  familyCompStructRealization_second _

/-- 元の両円柱を保持する高次比較全体も、全パラメータで全区間境界を固定する。 -/
lemma monicKTracedTripleDirectComparisonRealization_relative (n : ℕ) :
    ((SSet.boundary 1).ι ▷ (Δ[2] : SSet.{u})) ≫
        monicKTracedTripleDirectComparisonRealization F f g h n =
      fst (∂Δ[1] : SSet.{u}) Δ[2] ≫ (SSet.boundary 1).ι ≫
        monicKTracedUnaryCorrectionAtPoint F (f ≫ g ≫ h) n :=
  (monicKTracedTripleDirectComparisonData F f g h n).triangle_relative

end SerrePositivity.KST.SConstruction
