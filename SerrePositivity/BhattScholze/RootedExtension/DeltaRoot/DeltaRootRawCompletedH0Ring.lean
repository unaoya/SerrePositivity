module

public import SerrePositivity.BhattScholze.RootedExtension.DeltaRoot.DeltaRootRawCompletionReflection
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PDCompletion
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.TowerComplete

/-! # raw根環の実逐次H0の反射環とPD完備化環 -/

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

/-- 元の実逐次H0の加法とRaw作用を保つ反射環。 -/
@[instance_reducible] def deltaRootRawInternalH0CommRing : CommRing (H Z) :=
  (deltaRootRawInternalH0_isCompleteModuleReflection D d b).commRing

/-- 元の実Raw作用と一致する反射環の代数構造。 -/
@[instance_reducible] def deltaRootRawInternalH0Algebra :
    letI := deltaRootRawInternalH0CommRing D d b
    Algebra Raw (H Z) :=
  (deltaRootRawInternalH0_isCompleteModuleReflection D d b).algebra

/-- 元の線形比較は、同じ反射環構造についてRaw代数同型である。 -/
def deltaRootRawInternalPDAlgEquiv :
    letI := deltaRootRawInternalH0CommRing D d b
    letI := deltaRootRawInternalH0Algebra D d b
    letI := pdCompletionCommRing Raw p z
    letI := pdCompletionAlgebra Raw p z
    H Z ≃ₐ[Raw] PDCompletionH0 Raw p z := by
  letI := deltaRootRawInternalH0CommRing D d b
  letI := deltaRootRawInternalH0Algebra D d b
  letI := pdCompletionCommRing Raw p z
  letI := pdCompletionAlgebra Raw p z
  let e := deltaRootRawInternalPDLinearEquiv D d b
  let h := pairCompletionH0_isCompleteModuleReflection Raw (p : Raw) z
  have hT : ∀ j : Fin 2, IsModuleComplete Raw
      (pairKoszulCoordinates Raw (p : Raw) z j) (H Z) := by
    simpa only [map_natCast] using deltaRootRawInternalH0_isComplete D d b
  have h1 : e.symm (koszulCompletionH0Unit Raw
      (pairKoszulCoordinates Raw (p : Raw) z) 1) = (1 : H Z) := by
    apply e.injective
    rw [LinearEquiv.apply_symm_apply]
    exact (deltaRootRawInternalPDLinearEquiv_unit D d b 1).symm
  exact (AlgEquiv.ofLinearEquiv e.symm h1
    (h.linearMap_map_mul (H Z) hT e.symm.toLinearMap h1)).symm

/-- 代数同型の関数は、元の標準単位で正規化した線形比較そのもの。 -/
theorem deltaRootRawInternalPDAlgEquiv_apply (x : H Z) :
    deltaRootRawInternalPDAlgEquiv D d b x = deltaRootRawInternalPDLinearEquiv D d b x := rfl

/-- 代数比較も、すべてのraw係数の元のPD完備化像を保つ。 -/
theorem deltaRootRawInternalPDAlgEquiv_unit (x : Raw) :
    deltaRootRawInternalPDAlgEquiv D d b (deltaRootRawInternalH0Unit D d b x) =
      pdCompletionUnit Raw p z x := by
  rw [deltaRootRawInternalPDAlgEquiv_apply, deltaRootRawInternalPDLinearEquiv_unit,
    pdCompletionUnit_apply]

end SerrePositivity.BhattScholze
