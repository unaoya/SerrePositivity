module
public import SerrePositivity.DifferentialGraded.Derived.Evaluation
public import SerrePositivity.DifferentialGraded.Derived.Shift
public import SerrePositivity.DifferentialGraded.Module.Ring
public import Mathlib.CategoryTheory.Localization.LocalizerMorphism

/-! # 一対象 A の導来加群圏と既存 DerivedCategory の自然比較

既存の閉零加群圏同値は指定quasiIsoのクラスを保ち、反映する。
したがって局所化の一般論により、任意の明示的に選ばれた既存導来圏との同値を得る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A]

/-- 一対象環の指定準同型判定は既存複体の判定そのもの。 -/
lemma ringModuleQuasiIso_iff {M N : ModuleCategory A PUnit.{1}} (f : M ⟶ N) :
    moduleQuasiIso A PUnit.{1} f ↔
      QuasiIso ((moduleEvaluation A PUnit.{1} PUnit.unit).map f) := by
  constructor
  · exact fun h => h PUnit.unit
  · intro h x
    cases x
    exact h

/-- 一対象の加群圏同値を指定quasiIsoのlocalizerの射として公開する。 -/
def ringModuleLocalizer : LocalizerMorphism (moduleQuasiIso A PUnit.{1})
    (HomologicalComplex.quasiIso (ModuleCat A) (.up ℤ)) where
  functor := moduleEvaluation A PUnit.{1} PUnit.unit
  map _ _ f hf := (ringModuleQuasiIso_iff A f).1 hf

instance ringModuleLocalizerIsInduced : (ringModuleLocalizer A).IsInduced where
  inverseImage_eq := by
    ext M N f
    exact (ringModuleQuasiIso_iff A f).symm

instance ringModuleLocalizerFunctorIsEquivalence : (ringModuleLocalizer A).functor.IsEquivalence :=
  ringEvaluation_isEquivalence A

instance ringModuleLocalizerIsLocalizedEquivalence :
    (ringModuleLocalizer A).IsLocalizedEquivalence :=
  (ringModuleLocalizer A).isLocalizedEquivalence_of_isInduced

variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- U9で構成した導来評価自体が、一対象環では圏同値となる。 -/
instance ringDerivedEvaluationIsEquivalence :
    (moduleDerivedEvaluation A PUnit.{1} PUnit.unit).IsEquivalence := by
  let : CatCommSq (ringModuleLocalizer A).functor (moduleToDerived A PUnit.{1})
      (DerivedCategory.Q (C := ModuleCat A)) (moduleDerivedEvaluation A PUnit.{1} PUnit.unit) :=
    CatCommSq.mk (eqToIso (moduleDerivedEvaluation_fac A PUnit.{1} PUnit.unit).symm)
  exact (ringModuleLocalizer A).isEquivalence (moduleToDerived A PUnit.{1}) DerivedCategory.Q _

/-- 一対象 A の主導来加群圏と既存の A 複体導来圏の同値。 -/
def ringDerivedEquivalence : DerivedModuleCategory A PUnit.{1} ≌ DerivedCategory (ModuleCat A) :=
  (moduleDerivedEvaluation A PUnit.{1} PUnit.unit).asEquivalence

/-- 主局所化と既存複体の局所化を結ぶ比較自然同型。 -/
def ringDerivedEquivalence_fac :
    moduleToDerived A PUnit.{1} ⋙ (ringDerivedEquivalence A).functor ≅
      (ringModuleEquivalence A).functor ⋙ DerivedCategory.Q :=
  eqToIso (moduleDerivedEvaluation_fac A PUnit.{1} PUnit.unit)

/-- 一対象比較は導来圏の整数shiftとzero/add coherenceを保存する。 -/
instance ringModuleEquivalenceCommShift : (ringModuleEquivalence A).functor.CommShift ℤ :=
  moduleEvaluationCommShift A PUnit.{1} PUnit.unit

/-- 導来圏の一対象比較の整合的shift。 -/
instance ringDerivedEquivalenceCommShift : (ringDerivedEquivalence A).functor.CommShift ℤ :=
  moduleDerivedEvaluationCommShift A PUnit.{1} PUnit.unit

/-- 局所化比較の自然同型も整数shiftに整合する。 -/
instance ringDerivedEquivalenceFacCommShift :
    NatTrans.CommShift (ringDerivedEquivalence_fac A).hom ℤ := by
  change NatTrans.CommShift
    (eqToIso (moduleDerivedEvaluation_fac A PUnit.{1} PUnit.unit)).hom ℤ
  exact moduleDerivedEvaluationFacCommShift A PUnit.{1} PUnit.unit

end SerrePositivity.DifferentialGraded
