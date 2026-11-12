module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorSuppliedLaxComparisons
public import SerrePositivity.KST.SConstruction.DGOdotMilnorCompletedLandTamme
public import SerrePositivity.KST.SConstruction.DGKNativeValueComparison

/-!
概要：D2 の元二脚比較を native gluing から直接使い、同じ resolved 商と照合する。
方針：公開済みの二段同値を合成し、両射影と実 cone の全比較を保持する。
規約：Milnor 条件は明示引数。未分解 path 商との比較は要求しない。
使われ方：K-10 d② の供給と型照合。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local instance : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (DGOdotGluing R d) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnor_isDGPretriangulated R d

/-- 概要：native gluing から元代数二脚の Perf lax 模型への実同値。
方針：D2 の二段比較を合成する。規約：同じ元二脚を保持。使われ方：d②。 -/
def dgOdotTailNativePerfLaxEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorNativeMiddle R d).obj (dgOdotPerfLaxCategory R d).obj :=
  (dgOdotMilnorNativeLaxEquivalence R d).trans
    (dgOdotMilnorSuppliedOriginalLaxComparison R d).gluing

/-- 概要：元 gluing から同じ固定 ν の Perf 値への実 Yoneda 同値。
方針：native 完備性と D の dgPerfectYonedaInfinity_isIdempotentCompletion を
既存の同値判定へ渡す。規約：全 Perf の Small 性を要求しない。使われ方：d②。 -/
def dgOdotTailGluingNativeValueEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGOdotGluing R d))
    (dgKInputStableValue R (dgKUniverseInput.{u, u + 1, u + 1} R
      (DGOdotGluing R d))).obj :=
  (dgKNativeValueComparison_isQCatEquivalence R (DGOdotGluing R d)
    (dgOdotMilnorNativeMiddle_complete R d)).choose

/-- 概要：実 Perf(gluing) と元代数の Perf lax pullback の全同値。
方針：同じ Perf 評価と native Yoneda 同値の逆を既存合成比較へ接続する。
規約：元二脚の実 lax 模型を保持。使われ方：D2 G-1 f の d② 消費口。 -/
def dgOdotTailPerfectGluingLaxEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (PerfectDGModule R (DGOdotGluing R d)))
    (dgOdotPerfLaxCategory R d).obj :=
  ((dgKNativePerfectValueEquivalence R (DGOdotGluing R d)).trans
    (dgOdotTailGluingNativeValueEquivalence R d).symm).trans
      (dgOdotTailNativePerfLaxEquivalence R d)

/-- 概要：合成比較の左射影は元小 Perf 射影と指定因子同値の逆。
方針：供給済み全比較を native 比較で前合成する。規約：全単体を保持。
使われ方：元左脚の型照合。 -/
def dgOdotTailNativePerfLax_fst : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((dgOdotTailNativePerfLaxEquivalence R d).hom ≫
      (laxFst (dgOdotLowerExactMap R d) (dgOdotUpperExactMap R d)).hom)
    ((dgOdotMilnorNativeLaxComparison R d).hom ≫
      ((laxFst (dgOdotMilnorLaxYoneda R d) (dgOdotMilnorLaxCoefficient R d)).hom ≫
        (dgOdotMilnorLaxLeftInputEquivalence R d).inv)) := by
  simpa only [dgOdotTailNativePerfLaxEquivalence, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.trans,
    dgOdotMilnorNativeLaxComparison,
    Category.assoc] using
    (dgOdotMilnorSuppliedOriginalLaxComparison R d).fst.precomp
      (dgOdotMilnorNativeLaxComparison R d).hom

/-- 概要：合成比較の右射影も指定因子同値の逆を保持する。
方針：供給済み全比較を前合成する。規約：因子順序を保持。使われ方：元右脚照合。 -/
def dgOdotTailNativePerfLax_snd : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((dgOdotTailNativePerfLaxEquivalence R d).hom ≫
      (laxSnd (dgOdotLowerExactMap R d) (dgOdotUpperExactMap R d)).hom)
    ((dgOdotMilnorNativeLaxComparison R d).hom ≫
      ((laxSnd (dgOdotMilnorLaxYoneda R d) (dgOdotMilnorLaxCoefficient R d)).hom ≫
        (dgOdotMilnorLaxRightInputEquivalence R d).inv)) := by
  simpa only [dgOdotTailNativePerfLaxEquivalence, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.trans,
    dgOdotMilnorNativeLaxComparison,
    Category.assoc] using
    (dgOdotMilnorSuppliedOriginalLaxComparison R d).snd.precomp
      (dgOdotMilnorNativeLaxComparison R d).hom

/-- 概要：同じ合成比較後の lax 差は元 corner の実 cone 評価。
方針：D2 の供給済み cone 全比較の結合を照合する。
規約：corner 評価を選び直さない。使われ方：d② の実差の照合。 -/
def dgOdotTailNativePerfLax_cone : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((dgOdotTailNativePerfLaxEquivalence R d).hom ≫
      (exactLaxDifference (dgOdotLowerExactMap R d) (dgOdotUpperExactMap R d)).hom)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgOdotTargetFunctor R d) ≫ (dgOdotMilnorCornerEvaluation R d).hom) := by
  simpa only [dgOdotTailNativePerfLaxEquivalence, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.trans,
    dgOdotMilnorNativeLaxComparison,
    Category.assoc, DGOdotMilnorSuppliedOriginalConeComparison,
    dgOdotMilnorSuppliedOriginalLaxComparison] using
    dgOdotMilnorSuppliedOriginalConeComparison R d

/-- 概要：比較の逆を通る商射は同じ native resolved 射影を回収する。
方針：二段同値の指定単位を同じ実商へ後合成する。
規約：cell 平坦商を未分解商に戻さない。使われ方：d② の商辺照合。 -/
def dgOdotTailResolvedProjectionComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((dgOdotTailNativePerfLaxEquivalence R d).hom ≫
      ((dgOdotTailNativePerfLaxEquivalence R d).inv ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorResolvedProjection R d).hom))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorResolvedProjection R d).hom := by
  rw [← Category.assoc]
  simpa only [Category.id_comp] using
    (dgOdotTailNativePerfLaxEquivalence R d).homInvIso.postcomp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorResolvedProjection R d).hom
end SerrePositivity.KST.SConstruction
