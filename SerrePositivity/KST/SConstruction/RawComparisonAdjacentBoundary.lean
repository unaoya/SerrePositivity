module
public import SerrePositivity.KST.SConstruction.FullRelativeRawComparison
public import SerrePositivity.KST.SConstruction.FamilyCompositeImageClasses

/-! # 隣接段の比較問題の全境界の厳密な一致
概要：同じ両 raw 族の全段円柱の構造射像は、時刻の両端と入力境界で厳密に一致する。
方針：両端では元の raw 族の厳密な構造適合、入力境界では元の全境界固定式を使う。
規約：全境界の一致だけを結論し、相対比較の存在は別の高次 prism を必要とする。
使われ方：元の三入力比較を隣接段で相対的に整合させるための厳密な境界問題。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra
open SerrePositivity.InfinityCategories
open SerrePositivity.SimplicialModel
open scoped Simplicial
variable (X : OmegaSpectrum.{u}) (Y : KanSequence.{u}) {A U : SSet.{u}} (j : A ⟶ U)
  (a b : U ⟶ RawSpectrumMapping.space X Y)
  (H : ∀ n, SSet.Homotopy (a ≫ RawSpectrumMapping.evaluation X Y n)
    (b ≫ RawSpectrumMapping.evaluation X Y n))

/-- 隣接する両全円柱の像は、元の比較時刻の両端で厳密に一致する。 -/
lemma rawComparisonAdjacent_time (n : ℕ) :
    (U ◁ (SSet.boundary 1).ι) ≫ (H (n + 1)).h ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space =
      (U ◁ (SSet.boundary 1).ι) ≫ (H n).h ≫ RawSpectrumMapping.step X Y n := by
  have ha : (a ≫ RawSpectrumMapping.evaluation X Y (n + 1)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space =
      (a ≫ RawSpectrumMapping.evaluation X Y n) ≫ RawSpectrumMapping.step X Y n := by
    rw [Category.assoc, RawSpectrumMapping.evaluation_condition]
    simp only [Category.assoc]
  have hb : (b ≫ RawSpectrumMapping.evaluation X Y (n + 1)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space =
      (b ≫ RawSpectrumMapping.evaluation X Y n) ≫ RawSpectrumMapping.step X Y n := by
    rw [Category.assoc, RawSpectrumMapping.evaluation_condition]
    simp only [Category.assoc]
  let K := familyHomotopyEndpointTransport
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (H (n + 1))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space)) ha.symm hb
  let L := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (H n) (RawSpectrumMapping.step X Y n)
  have h := (HomotopyEndpointComparison.boundary_eq K).trans
    (HomotopyEndpointComparison.boundary_eq L).symm
  simpa only [K, L, familyHomotopyEndpointTransport_h, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp,
    Category.assoc] using h

/-- 入力境界を固定した隣接円柱の像は、二つの全境界の和で厳密に一致する。 -/
lemma rawComparisonAdjacent_boundary
    (hr : ∀ n, (j ▷ (Δ[1] : SSet.{u})) ≫ (H n).h =
      fst A Δ[1] ≫ j ≫ a ≫ RawSpectrumMapping.evaluation X Y n) (n : ℕ) :
    fullCylinderBoundaryInclusion j ≫ (H (n + 1)).h ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space =
      fullCylinderBoundaryInclusion j ≫ (H n).h ≫ RawSpectrumMapping.step X Y n := by
  apply (fullCylinderBoundary_map_iff j _ _).mpr
  constructor
  · exact rawComparisonAdjacent_time X Y a b H n
  · simp only [← Category.assoc]
    rw [hr (n + 1), hr n]
    simp only [Category.assoc]
    rw [RawSpectrumMapping.evaluation_condition]

end SerrePositivity.KST.SConstruction
