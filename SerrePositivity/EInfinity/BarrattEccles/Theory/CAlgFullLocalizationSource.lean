module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.CAlgCoefficientSourceComparison
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelHammockLocalization

/-!
# 元の全代数の nerve を始域とする CAlg の局所化

## 概要
HA §1.3.4 の導来関手を、Barratt–Eccles の厳密代数全体の上で比較する。

## 方針
cofibrant 入力の局所化を、全代数とその置換の弱変形に沿って移す。

## 規約
通常圏の対象は元の代数で、Hom の宇宙だけを上げる。

## 使われ方
M13 の導来随伴、零次ホモロジーの関手化。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory SSet _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization HomologicalComplex
open SerrePositivity.InfinityCategories
open scoped Simplicial

variable (A : Type u) [CommRing A]

/-- 全代数の相対圏。弱同値は同じ底の擬同型。 -/
def allAlgebraRelativeCategory : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u + 1} where
  category := Cat.of (ULiftHom.{u + 1} (operad A).Algebra)
  weakEquivalences := (quasiIso (ModuleCat A) (.up ℤ)).inverseImage
    ((ULiftHom.down.{u, u + 1, u + 1} (C := (operad A).Algebra)) ⋙
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget (operad A))
  isMultiplicative := inferInstance

/-- 全相対圏から元の代数圏への通常の忘却。 -/
abbrev allAlgebraDKDown : (allAlgebraRelativeCategory A).category ⥤ (operad A).Algebra :=
  ULiftHom.down.{u, u + 1, u + 1} (C := (operad A).Algebra)

/-- 元の代数圏から全相対圏へ Hom の宇宙を上げる。 -/
abbrev allAlgebraDKUp : (operad A).Algebra ⥤ (allAlgebraRelativeCategory A).category :=
  ULiftHom.up.{u, u + 1, u + 1} (C := (operad A).Algebra)

/-- cofibrant 相対圏の全相対圏への包含。 -/
def allAlgebraDKInclusion :
    (cofibrantAlgebraRelativeCategory A).category ⥤ (allAlgebraRelativeCategory A).category :=
  cofibrantAlgebraDKInclusion A ⋙ allAlgebraDKUp A

/-- 全相対圏での元の関手的置換。 -/
def allAlgebraDKReplacement :
    (allAlgebraRelativeCategory A).category ⥤ (cofibrantAlgebraRelativeCategory A).category :=
  allAlgebraDKDown A ⋙ cofibrantAlgebraDKReplacement A

/-- 置換から元の全相対圏の対象への augmentation。 -/
def allAlgebraDKReplacementAugmentation :
    allAlgebraDKReplacement A ⋙ allAlgebraDKInclusion A ⟶
      𝟭 (allAlgebraRelativeCategory A).category where
  app X := ULift.up ((framedLimitProbeComparisonNatTrans A).app
    ((allAlgebraDKDown A).obj X))
  naturality X Y g := by
    apply ULift.ext
    exact (framedLimitProbeComparisonNatTrans A).naturality ((allAlgebraDKDown A).map g)

/-- 全代数の弱同値による局所化の源。 -/
def allAlgebraCAlgSource : nerve (allAlgebraRelativeCategory A).category ⟶ CAlg_R A :=
  nerveMap (allAlgebraDKReplacement A) ≫ cAlgLocalizationSource A

/-- 全代数からの源も、同じ CAlg を局所化として実現する。 -/
lemma allAlgebraCAlgSource_isLocalization :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization (allAlgebraCAlgSource A) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.weakNerveEdges (allAlgebraRelativeCategory A)) := by
  let C := cofibrantAlgebraRelativeCategory A
  let B := allAlgebraRelativeCategory A
  let I : LocalizerMorphism C.weakEquivalences B.weakEquivalences :=
    ⟨allAlgebraDKInclusion A, fun _ _ _ h => h⟩
  let P : LocalizerMorphism B.weakEquivalences C.weakEquivalences :=
    ⟨allAlgebraDKReplacement A, fun _ _ g h =>
      framedLimitProbeFunctor_map_quasiIso A ((allAlgebraDKDown A).map g) h⟩
  let η := allAlgebraDKReplacementAugmentation A
  let θ := cofibrantAlgebraDKReplacementAugmentation A
  have hη (X : B.category) : B.weakEquivalences (η.app X) :=
    framedLimitProbeComparison_quasiIso A ((allAlgebraDKDown A).obj X)
  have hθ (X : C.category) : C.weakEquivalences (θ.app X) :=
    framedLimitProbeComparison_quasiIso A ((cofibrantAlgebraDKInclusion A).obj X)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.isLocalization_of_weakDeformation
    (nerveMap I.functor) (nerveMap P.functor) (cAlgLocalizationSource A)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.weakNerveEdges C) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.weakNerveEdges B) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.relativeNerve_mapsWeak I) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.relativeNerve_mapsWeak P)
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy η) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy θ)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.relativeNerve_homotopy_component_weak η hη)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.relativeNerve_homotopy_component_weak θ hθ) (cAlgLocalizationSource_isLocalization A)

end SerrePositivity.EInfinity.BarrattEccles
