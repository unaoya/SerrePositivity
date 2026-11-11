module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFFirstProperties
public import SerrePositivity.KST.SConstruction.PointedEnrichedCylinderComponents
public import SerrePositivity.KST.SConstruction.PointedCylinderOmegaCriterion

/-! # 元の零段を保持する最初の実 BF Ω 条件
概要：同じ最初の単射構造射の随伴は全基点 π 同型。
方針：実円柱の基点固定成分と、元の B₀ 比較の全基点 π 同型を使う。
規約：元の零段は ΩB₀。使われ方：再帰 BF 列の Ω 条件の基底。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalClosed SSet Spectra
open SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 元の零段の同じ Kan 性を、構造随伴の型にも保持する。 -/
local instance presentedPerfectDGBFFirstOmegaZero_kanComplex (C : PerfDGInput.{u, v} A) :
    KanComplex (((presentedPerfectDGBFZeroFunctor A).obj C).obj).right :=
  presentedPerfectDGBFZero_kanComplex A C

/-- 同じ最初の段の loop の Kan 性を閉構造の型で保持する。 -/
local instance presentedPerfectDGBFFirstOmegaLoop_kanComplex (C : PerfDGInput.{u, v} A) :
    KanComplex ((ihom PointedSimplicialSet.circle.{max (u + 1) v}).obj
      ((presentedPerfectDGBFFirstFunctor A).obj C).obj).right :=
  loopSpace_kanComplex _

/-- 元の零段と同じ評価から作った最初の実構造射は Ω 条件を満たす。 -/
lemma presentedPerfectDGBFFirstStructureAdjoint_piIsomorphism
    (C : PerfDGInput.{u, v} A) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (curry
      (show _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (((presentedPerfectDGBFZeroFunctor A).obj C).obj) ⟶
        ((presentedPerfectDGBFFirstFunctor A).obj C).obj from
          presentedPerfectDGBFFirstStructureMap A C)).right := by
  apply evaluationCylinderAdjoint_piIsomorphism
    (show ((presentedPerfectDGBFBaseFunctor A).obj C).obj ⟶
      ((presentedPerfectDGBFFirstFunctor A).obj C).obj from
        presentedPerfectDGBFFirstComparison A C)
    (presentedPerfectDGBFFirstComparison_piIsomorphism A C)
  exact pointedEnrichedMonicReplacementSource_component
    (presentedPerfectDGBFZeroSuspensionFunctor A) (presentedPerfectDGBFBaseFunctor A)
    (presentedPerfectDGBFZeroEvaluation A) (presentedPerfectDGBFZeroEvaluation_whisker A) C

end SerrePositivity.KST.SConstruction
