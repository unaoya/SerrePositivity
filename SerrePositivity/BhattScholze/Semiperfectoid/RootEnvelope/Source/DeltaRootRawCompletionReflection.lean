module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootEnvelope.Source.DeltaRootRawCompletionRestriction
public import SerrePositivity.BhattScholze.Andre.RootedExtension.IteratedPDH0Reflection
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.TowerComplete

/-! # raw根環の実逐次完備化H0の二座標反射 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (b : σ → A)
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => deltaRootRelationFamily (p := p) b
local notation "Raw" => DeltaAdjoinDivision E (MvPolynomial.C d) r
local notation "c" => algebraMap A Raw
local notation "a" => (c (p : A))
local notation "z" => (c d)
local notation "M" => CategoryTheory.Functor.obj
  (DerivedCategory.singleFunctor (ModuleCat Raw) 0) (ModuleCat.of Raw Raw)
local notation "Cp" => derivedComplexCompletionFunctor Raw a
local notation "Y" => CategoryTheory.Functor.obj (derivedComplexCompletionFunctor Raw a) M
local notation "Z" => DeltaRootRawInternalIteratedCompletion D d b
local notation "H" => CategoryTheory.Functor.obj (DerivedCategory.homologyFunctor (ModuleCat Raw) 0)
local notation "U" => CategoryTheory.NatTrans.app (derivedComplexCompletionUnit Raw a) M ≫
  CategoryTheory.NatTrans.app (derivedComplexCompletionUnit Raw z) Y

/-- raw自身の実逐次完備化から誘導される、元のRaw線形標準単位。 -/
def deltaRootRawInternalH0Unit : Raw →ₗ[Raw] H Z :=
  (((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat Raw) 0).inv.app
    (ModuleCat.of Raw Raw)) ≫ (DerivedCategory.homologyFunctor (ModuleCat Raw) 0).map U).hom

/-- raw自身の実逐次対象は、二つ目の完備化後にも最初の座標について完備。 -/
theorem deltaRootRawInternalIterated_isComplete_first : IsComplete Raw a Z := by
  exact iteratedPDCompletion_isComplete_first Raw a z

/-- raw自身の実逐次H0は両座標について導来完備。 -/
theorem deltaRootRawInternalH0_isComplete :
    ∀ j : Fin 2, IsModuleComplete Raw (pairKoszulCoordinates Raw a z j) (H Z) := by
  exact iteratedPDH0_isComplete Raw a z

/-- 同じ標準単位は、両座標について完備な加群への写像を一意に決定する。 -/
theorem deltaRootRawInternalH0_isCompleteModuleReflection :
    IsCompleteModuleReflection Raw (pairKoszulCoordinates Raw a z) (H Z)
      (deltaRootRawInternalH0Unit D d b 1) := by
  simpa only [deltaRootRawInternalH0Unit, DeltaRootRawInternalIteratedCompletion,
    iteratedPDH0Unit] using iteratedPDH0_isCompleteModuleReflection Raw a z

/-- 二つの実H0反射の間には、元の線形標準単位を保つ同型がある。 -/
theorem exists_deltaRootRawInternalPDLinearEquiv :
    ∃ e : H Z ≃ₗ[Raw] PDCompletionH0 Raw p z,
      ∀ x : Raw, e (deltaRootRawInternalH0Unit D d b x) =
        koszulCompletionH0Unit Raw (pairKoszulCoordinates Raw (p : Raw) z) x := by
  simpa only [deltaRootRawInternalH0Unit, DeltaRootRawInternalIteratedCompletion,
    iteratedPDH0Unit] using
      exists_iteratedPDH0LinearEquiv Raw a z p (map_natCast c p)

/-- 元のRaw線形単位で正規化した、実逐次H0から実PD完備化H0への同型。 -/
def deltaRootRawInternalPDLinearEquiv : H Z ≃ₗ[Raw] PDCompletionH0 Raw p z :=
  (exists_deltaRootRawInternalPDLinearEquiv D d b).choose

/-- 比較は全raw係数の元の完備化像を保つ。 -/
theorem deltaRootRawInternalPDLinearEquiv_unit (x : Raw) :
    deltaRootRawInternalPDLinearEquiv D d b (deltaRootRawInternalH0Unit D d b x) =
      koszulCompletionH0Unit Raw (pairKoszulCoordinates Raw (p : Raw) z) x :=
  (exists_deltaRootRawInternalPDLinearEquiv D d b).choose_spec x

/-- 元の実根添加源の実H0とrawのPD完備化H0の具体的A線形同型。 -/
def deltaRootSourcePDH0Iso :
    (DerivedCategory.homologyFunctor (ModuleCat A) 0).obj
        (DeltaRootSourceIteratedPDCompletion D d b).obj ≅
      (ModuleCat.restrictScalars c).obj (ModuleCat.of Raw (PDCompletionH0 Raw p z)) :=
  deltaRootSourceInternalRawH0Iso D d b ≪≫
    (ModuleCat.restrictScalars c).mapIso (deltaRootRawInternalPDLinearEquiv D d b).toModuleIso

end SerrePositivity.BhattScholze
