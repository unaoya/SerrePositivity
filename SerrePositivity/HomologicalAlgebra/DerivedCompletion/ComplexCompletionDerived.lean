module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ComplexCompletionQuasiIso

/-! # 実導来圏上の主元Koszul完備化候補

準同型同値不変性により、複体上の具体的な構成を実際の導来圏に降ろす。
標準射とその同型性の証明は別に行う。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R]

/-- 完備化候補の実導来像は準同型同値を反転する。 -/
theorem complexCompletionFunctor_inverts_quasiIso (a : R) :
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)).IsInvertedBy
      (complexCompletionFunctor R a ⋙ DerivedCategory.Q) := by
  intro K L f hf
  have : QuasiIso f := hf
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat R) _).mpr
    (complexCompletionFunctor_map_quasiIso R a f)

/-- 主元Koszul冪塔のholimによる候補を実導来圏の関手として構成する。 -/
def derivedComplexCompletionFunctor (a : R) :
    ConcreteDerivedCategory R ⥤ ConcreteDerivedCategory R :=
  Localization.lift (complexCompletionFunctor R a ⋙ DerivedCategory.Q)
    (complexCompletionFunctor_inverts_quasiIso R a) DerivedCategory.Q

/-- 導来圏の関手は、複体の具体的なholimモデルと自然に一致する。 -/
def derivedComplexCompletionComparison (a : R) :
    DerivedCategory.Q ⋙ derivedComplexCompletionFunctor R a ≅
      complexCompletionFunctor R a ⋙ DerivedCategory.Q :=
  Localization.fac (complexCompletionFunctor R a ⋙ DerivedCategory.Q)
    (complexCompletionFunctor_inverts_quasiIso R a) DerivedCategory.Q

/-- 代表複体の比較は元の複体の射と両立する。 -/
@[reassoc] theorem derivedComplexCompletionComparison_naturality (a : R)
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) :
    (derivedComplexCompletionFunctor R a).map (DerivedCategory.Q.map f) ≫
      (derivedComplexCompletionComparison R a).hom.app L =
    (derivedComplexCompletionComparison R a).hom.app K ≫
      DerivedCategory.Q.map ((complexCompletionFunctor R a).map f) :=
  (derivedComplexCompletionComparison R a).hom.naturality f

/-- 実導来圏の任意対象の完備化候補は導来完備である。 -/
theorem derivedComplexCompletionFunctor_isComplete (a : R) (X : ConcreteDerivedCategory R) :
    IsComplete R a ((derivedComplexCompletionFunctor R a).obj X) := by
  let K := DerivedCategory.Q.objPreimage X
  let e : complexCompletionObject R a K ≅ (derivedComplexCompletionFunctor R a).obj X :=
    (derivedComplexCompletionComparison R a).symm.app K ≪≫
      (derivedComplexCompletionFunctor R a).mapIso (DerivedCategory.Q.objObjPreimageIso X)
  exact isComplete_of_iso R a e (complexCompletionObject_isComplete R a K)

end SerrePositivity.DerivedCompletion
