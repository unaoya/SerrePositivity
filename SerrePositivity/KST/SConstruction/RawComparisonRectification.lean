module
public import SerrePositivity.KST.SConstruction.RawComparisonRectificationStages

/-! # 累積相対補正による全段 raw 比較の実円柱
概要：前段までの補正を反映した厳密な全段円柱を、一つの raw 写像空間の円柱へ束ねる。
方針：同じ累積帰納の全段評価と strict な構造適合を RawSpectrumMapping.lift に渡す。
規約：元の二族を両端に厳密に持ち、零段の元の全円柱をそのまま保持する。
使われ方：直接厳密化と BF 合成の raw 族の実比較、および指定境界付き BF 延長。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet Spectra
open scoped Simplicial
variable (X : OmegaSpectrum.{u}) (Y : KanSequence.{u}) {U : SSet.{u}}
  (a b : U ⟶ RawSpectrumMapping.space X Y)
  (H : ∀ n, SSet.Homotopy (a ≫ RawSpectrumMapping.evaluation X Y n)
    (b ≫ RawSpectrumMapping.evaluation X Y n))
  (L : ∀ n, SSet.Homotopy
    ((H (n + 1)).h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space)
    ((H n).h ≫ RawSpectrumMapping.step X Y n))
  (hL : ∀ n, ((U ◁ (SSet.boundary 1).ι) ▷ (Δ[1] : SSet.{u})) ≫ (L n).h =
    CartesianMonoidalCategory.fst (U ⊗ (SSet.boundary 1).toSSet) Δ[1] ≫
      (U ◁ (SSet.boundary 1).ι) ≫ (H (n + 1)).h ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space)

/-- 累積補正済みの全段の実円柱を、一つの raw 族に束ねる。 -/
def rawComparisonRectificationMap : U ⊗ (Δ[1] : SSet.{u}) ⟶ RawSpectrumMapping.space X Y :=
  RawSpectrumMapping.lift X Y (fun n => (rawComparisonStage X Y a b H L hL n).val.h)
    (rawComparisonStage_condition X Y a b H L hL)

/-- 全写像空間の円柱の各段は、同じ累積補正済み円柱を厳密に回収する。 -/
lemma rawComparisonRectificationMap_evaluation (n : ℕ) :
    rawComparisonRectificationMap X Y a b H L hL ≫ RawSpectrumMapping.evaluation X Y n =
      (rawComparisonStage X Y a b H L hL n).val.h :=
  RawSpectrumMapping.lift_evaluation _ _ _ _ _

/-- 元の二つの raw 族を両端に持つ、全段の実比較円柱。 -/
def rawComparisonRectification : SSet.Homotopy a b where
  h := rawComparisonRectificationMap X Y a b H L hL
  h₀ := by
    apply RawSpectrumMapping.hom_ext X Y
    intro n
    change (SSet.ι₀ ≫ rawComparisonRectificationMap X Y a b H L hL) ≫
      RawSpectrumMapping.evaluation X Y n = a ≫ RawSpectrumMapping.evaluation X Y n
    rw [Category.assoc, rawComparisonRectificationMap_evaluation]
    exact (rawComparisonStage X Y a b H L hL n).val.h₀
  h₁ := by
    apply RawSpectrumMapping.hom_ext X Y
    intro n
    change (SSet.ι₁ ≫ rawComparisonRectificationMap X Y a b H L hL) ≫
      RawSpectrumMapping.evaluation X Y n = b ≫ RawSpectrumMapping.evaluation X Y n
    rw [Category.assoc, rawComparisonRectificationMap_evaluation]
    exact (rawComparisonStage X Y a b H L hL n).val.h₁
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 零段の全実円柱を一切変更せず保持する。 -/
lemma rawComparisonRectification_zero :
    (rawComparisonRectification X Y a b H L hL).h ≫ RawSpectrumMapping.evaluation X Y 0 =
      (H 0).h :=
  rawComparisonRectificationMap_evaluation X Y a b H L hL 0

end SerrePositivity.KST.SConstruction
