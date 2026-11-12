module
public import SerrePositivity.KST.SConstruction.SourceFixedBoundaryComposition
public import SerrePositivity.KST.SConstruction.FamilyCylinderBoundaryAdjustment
public import SerrePositivity.KST.SConstruction.RawStageComparisonImage

/-! # 累積補正を保持する全 raw 比較の逐次段
概要：前段までの実補正を反映し、次段円柱の射影を補正済み前段の構造射像へ合わせる。
方針：元の適合比較と前段補正の像を全境界固定空間内で合成し、同じ全円柱を持ち上げる。
規約：両端・全区間境界・元の比較からの実補正を各段に保存する。
使われ方：零段からの帰納と RawSpectrumMapping.lift による全段比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra HomotopicalAlgebra
open SerrePositivity.InfinityCategories
open SerrePositivity.SimplicialModel.LargeParameterHomotopy
open SSet.modelCategoryQuillen
open scoped Simplicial
variable (X : OmegaSpectrum.{u}) (Y : KanSequence.{u}) {U : SSet.{u}}
  (a b : U ⟶ RawSpectrumMapping.space X Y)
  (H : ∀ n, SSet.Homotopy (a ≫ RawSpectrumMapping.evaluation X Y n)
    (b ≫ RawSpectrumMapping.evaluation X Y n))

/-- 各段の比較円柱と、元の比較からの全境界固定実補正。 -/
structure RawComparisonStage (n : ℕ) where
  /-- 同じ二つの raw 評価を両端に持つ補正済み円柱。 -/
  val : SSet.Homotopy (a ≫ RawSpectrumMapping.evaluation X Y n)
    (b ≫ RawSpectrumMapping.evaluation X Y n)
  /-- 元の比較円柱からの全実二次元補正。 -/
  correction : SSet.Homotopy (H n).h val.h
  /-- 元の全区間境界を補正の全時刻で固定する。 -/
  boundary : ((U ◁ (SSet.boundary 1).ι) ▷ (Δ[1] : SSet.{u})) ≫ correction.h =
    fst (U ⊗ (SSet.boundary 1).toSSet) Δ[1] ≫ (U ◁ (SSet.boundary 1).ι) ≫ (H n).h

/-- 零段には新しい比較円柱を選ばず、元の円柱と定数な補正を保持する。 -/
def rawComparisonBase : RawComparisonStage X Y a b H 0 where
  val := H 0
  correction := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl (H 0).h
  boundary := whiskerRight_fst_assoc _ _ _

variable
  (L : ∀ n, SSet.Homotopy
    ((H (n + 1)).h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space)
    ((H n).h ≫ RawSpectrumMapping.step X Y n))
  (hL : ∀ n, ((U ◁ (SSet.boundary 1).ι) ▷ (Δ[1] : SSet.{u})) ≫ (L n).h =
    fst (U ⊗ (SSet.boundary 1).toSSet) Δ[1] ≫ (U ◁ (SSet.boundary 1).ι) ≫
      (H (n + 1)).h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space)

local instance rawComparisonRestrictionFibration (n : ℕ) :
    Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre_fibration _ _

/-- 累積前段補正を元の適合比較へ相対合成して、同じ全比較を次段で持ち上げる。 -/
def rawComparisonNext (n : ℕ) (s : RawComparisonStage X Y a b H n) :
    {t : RawComparisonStage X Y a b H (n + 1) //
      t.val.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space =
        s.val.h ≫ RawSpectrumMapping.step X Y n} := by
  let j := U ◁ (SSet.boundary 1).ι
  let step := RawSpectrumMapping.step X Y n
  let K := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp s.correction step
  have hK : (j ▷ (Δ[1] : SSet.{u})) ≫ K.h =
      fst (U ⊗ (SSet.boundary 1).toSSet) Δ[1] ≫ j ≫ ((H n).h ≫ step) := by
    change (j ▷ (Δ[1] : SSet.{u})) ≫ s.correction.h ≫ step = _
    rw [← Category.assoc, s.boundary, Category.assoc, Category.assoc]
  let C := sourceFixedBoundaryComposition j (L n) K (hL n) hK
  let D := cylinderBoundaryAdjustmentData
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space) (H (n + 1))
    (rawStageComparisonImage X Y a b n s.val) C.homotopy C.relative
  exact ⟨⟨D.val, D.comparison, D.boundary⟩, D.projection⟩

/-- 元の零段からの累積帰納で、全段の実比較と相対補正を内部構成する。 -/
def rawComparisonStage : (n : ℕ) → RawComparisonStage X Y a b H n
  | 0 => rawComparisonBase X Y a b H
  | n + 1 => (rawComparisonNext X Y a b H L hL n (rawComparisonStage n)).val

/-- 隣接する二段の実比較円柱は厳密な全射の等号で構造適合する。 -/
lemma rawComparisonStage_condition (n : ℕ) :
    (rawComparisonStage X Y a b H L hL (n + 1)).val.h ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space =
    (rawComparisonStage X Y a b H L hL n).val.h ≫ RawSpectrumMapping.step X Y n :=
  (rawComparisonNext X Y a b H L hL n (rawComparisonStage X Y a b H L hL n)).property

end SerrePositivity.KST.SConstruction
