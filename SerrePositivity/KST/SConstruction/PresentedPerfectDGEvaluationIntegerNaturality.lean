module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGEvaluationNaturality
public import SerrePositivity.KST.SConstruction.StableKFunctorIsoInvariance

/-! # 元の実 Perf 評価による整数 π 比較の入力自然性
概要：実評価四角形の native 関手同型を、元の BF K 射の整数 π の自然性へ移す。
方針：全段の基点固定成分不変性と元の整数 π の合成則を使う。
規約：評価射と厳密 dg 入力射を保持する。使われ方：新 BF K と元の dgK の比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Spectra
open SerrePositivity.InfinityCategories SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の実 Perf 評価四角形は、同じ実 BF K 射の全整数 π 作用で可換。 -/
lemma presentedPerfectDGBFEvaluation_integer_naturality
    {X Y : PerfDGInput.{u, v} A} (f : X ⟶ Y) (j : ℤ)
    (a : OmegaSpectrum.homotopyGroup
      (kOmegaSpectrum (stableCategoryModel (presentedPerfectDGStableCategory A X))) j) :
    kHomotopyMap (perfectDGStableMap A X Y f.down) j
        (OmegaSpectrum.homotopyMap (presentedPerfectDGBFEvaluationKMap A X) j a) =
      OmegaSpectrum.homotopyMap (presentedPerfectDGBFEvaluationKMap A Y) j
        (kHomotopyMap (presentedPerfectDGBFInputStableMap A f) j a) := by
  let l := (presentedPerfectDGBFEvaluationEquivalence A X).hom ≫
    perfectDGStableMap A X Y f.down
  let r := presentedPerfectDGBFInputStableMap A f ≫
    (presentedPerfectDGBFEvaluationEquivalence A Y).hom
  have hl : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor l.val :=
    @_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isExactFunctor_comp _ _ _ _ _
      (presentedPerfectDGEvaluationNerve_isExactFunctor A X)
      (perfectDGExtensionNerve_isExactFunctor A X Y f.down)
  have hr : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor r.val :=
    @_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isExactFunctor_comp _ _ _ _ _
      (presentedPerfectDGActionNerve_isExactFunctor A X Y f.down)
      (presentedPerfectDGEvaluationNerve_isExactFunctor A Y)
  have h := kHomotopyMap_eq_of_exact_functorIso l r hl hr
    (presentedPerfectDGBFEvaluationInputComparison A f) j
  rw [kHomotopyMap_comp, kHomotopyMap_comp] at h
  exact DFunLike.congr_fun h a

end SerrePositivity.KST.SConstruction
