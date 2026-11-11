module
public import SerrePositivity.KST.SConstruction.MonicKPrismNativeLevelComparison
public import SerrePositivity.KST.SConstruction.FamilyCompStructImage

/-! # 元の各段比較三角形の二つの全構造射像
概要：前段比較の構造射像と次段比較の射影を、同じ両端の元の実円柱として表示する。
方針：同じ raw 評価の strict 適合式で端点だけを合わせ、元の全 span 二単体を後合成する。
規約：元の各段比較円柱・三角形の全実写像を保持する。
使われ方：二組の構造三角形と合わせる四三角形の比較。
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
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {x y z : I} (f : x ⟶ y) (g : y ⟶ z)

/-- 前段の元の実比較円柱の全構造射像を、同じ次段射影の両端へ表示する。 -/
def monicKPrismNativePreviousComparison (n : ℕ) :=
  familyHomotopyEndpointTransport
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (monicKPrismNativeLevelComparison F f g n)
      (RawSpectrumMapping.step (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z)) n))
    (monicKPrismNativeDirectRaw_condition F f g n)
    (monicKPrismNativeRawComposition_condition F f g n).symm

/-- 次段の元の実比較円柱全体を、同じ源構造射へ制限する。 -/
def monicKPrismNativeProjectedComparison (n : ℕ) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (monicKPrismNativeLevelComparison F f g (n + 1))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((kOmegaSpectrum (F.obj x)).sigma n)
      ((kKanSequence (F.obj z)).level (n + 1)).space)

/-- 端点の表示変更でも前段円柱の全実構造射像そのものを保つ。 -/
lemma monicKPrismNativePreviousComparison_h (n : ℕ) :
    (monicKPrismNativePreviousComparison F f g n).h =
      (monicKPrismNativeLevelComparison F f g n).h ≫
        RawSpectrumMapping.step (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z)) n :=
  familyHomotopyEndpointTransport_h _ _ _

/-- 前段の全 span 三角形を同じ構造射で写した実三角形。 -/
def monicKPrismNativePreviousComparisonTriangle (n : ℕ) : SSet.Edge.CompStruct
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (monicKPrismNativeDirectPreviousStructureCylinder F f g n)))
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (monicKPrismNativePreviousComparison F f g n)))
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (monicKPrismNativePreviousStructureCylinder F f g n))) :=
  familyCompStructImage (monicKPrismNativeLevelComparisonData F f g n).triangle
    (RawSpectrumMapping.step (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z)) n)
    _ _ _ (familyHomotopyEndpointTransport_h _ _ _)
      (monicKPrismNativePreviousComparison_h F f g n) (familyHomotopyEndpointTransport_h _ _ _)

/-- 次段の全 span 三角形を同じ源構造射へ制限した実三角形。 -/
def monicKPrismNativeProjectedComparisonTriangle (n : ℕ) : SSet.Edge.CompStruct
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (monicKPrismNativeDirectProjectedStructureCylinder F f g n)))
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (monicKPrismNativeProjectedComparison F f g n)))
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (monicKPrismNativeProjectedStructureCylinder F f g n))) :=
  familyCompStructImage (monicKPrismNativeLevelComparisonData F f g (n + 1)).triangle
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((kOmegaSpectrum (F.obj x)).sigma n)
      ((kKanSequence (F.obj z)).level (n + 1)).space) _ _ _ rfl rfl rfl

/-- 前段の実三角形全体も、元の同じ span 三角形の全構造射像。 -/
lemma monicKPrismNativePreviousComparisonTriangle_map (n : ℕ) :
    familyCompStructRealization (monicKPrismNativePreviousComparisonTriangle F f g n) =
      monicKPrismNativeLevelComparisonMap F f g n ≫
        RawSpectrumMapping.step (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z)) n :=
  familyCompStructImage_map _ _ _ _ _ _ _ _

/-- 次段の実三角形全体も、元の同じ span 三角形の全源制限。 -/
lemma monicKPrismNativeProjectedComparisonTriangle_map (n : ℕ) :
    familyCompStructRealization (monicKPrismNativeProjectedComparisonTriangle F f g n) =
      monicKPrismNativeLevelComparisonMap F f g (n + 1) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((kOmegaSpectrum (F.obj x)).sigma n)
          ((kKanSequence (F.obj z)).level (n + 1)).space :=
  familyCompStructImage_map _ _ _ _ _ _ _ _

end SerrePositivity.KST.SConstruction
