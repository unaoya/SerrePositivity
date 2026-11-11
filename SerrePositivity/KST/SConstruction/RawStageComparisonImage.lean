module
public import SerrePositivity.KST.SConstruction.FamilyCylinderEndpointAdjustment
public import SerrePositivity.KST.Spectra.RawSpectrumMapping

/-! # 厳密な raw 族の段円柱の構造射像
概要：同じ raw 二族の段円柱を、次段源制限と同じ両端の円柱として表示する。
方針：全 raw 評価の strict 適合式で両端だけを合わせ、実円柱全体を後合成する。
規約：円柱の全時刻の写像は同じ構造射像そのもの。
使われ方：補正済み前段を標的とする累積帰納の基底円柱。
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

/-- 全 raw 族の各段評価の strict な構造適合。 -/
lemma rawStageFamily_condition (n : ℕ) :
    (a ≫ RawSpectrumMapping.evaluation X Y (n + 1)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space =
    (a ≫ RawSpectrumMapping.evaluation X Y n) ≫ RawSpectrumMapping.step X Y n := by
  simpa only [Category.assoc] using congrArg (a ≫ ·)
    (RawSpectrumMapping.evaluation_condition X Y n)

/-- 元の段円柱の全構造射像を、次段射影の厳密な両端の間に表示する。 -/
def rawStageComparisonImage (n : ℕ)
    (H : SSet.Homotopy (a ≫ RawSpectrumMapping.evaluation X Y n)
      (b ≫ RawSpectrumMapping.evaluation X Y n)) :
    SSet.Homotopy
      ((a ≫ RawSpectrumMapping.evaluation X Y (n + 1)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space)
      ((b ≫ RawSpectrumMapping.evaluation X Y (n + 1)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space) where
  h := H.h ≫ RawSpectrumMapping.step X Y n
  h₀ := by
    rw [← Category.assoc, H.h₀]
    exact (rawStageFamily_condition X Y a n).symm
  h₁ := by
    rw [← Category.assoc, H.h₁]
    exact (rawStageFamily_condition X Y b n).symm
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

end SerrePositivity.KST.SConstruction
