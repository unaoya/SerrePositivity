module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineCompletedCoverSquare
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineLineOrdinaryHomology

/-!
# 元の指定被覆の始域・終域のホモロジー同型

## 概要
元の形式の係数同型と元の指定e_targetから零次・一次の比較を作る。

## 方針
同じ標準ホモロジー分解同型と元の指定零延長の同型を合成する。

## 規約
終域は元の完備Tot比較の同型から構成する。

## 使われ方
HT04.R2の型つきの零次・一次の正方形。
-/

public noncomputable section
universe u
open CategoryTheory HomologicalComplex
open scoped TensorProduct ChangeOfRings
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded HTComparisonResolution HTUniversalCrystallineInput SerrePositivity.DeRham
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 元の基底の生成元をpと仮定しない、同じ形式の係数同型。 -/
def affineCoverFormsEquiv (P : OrientedPrism p A) (i : ℕ) :
    (ModuleCat.extendScalars (Construction61.crystallineCoverMap P).toRingHom).obj
      ((ModuleCat.restrictScalars (affineBaseToPolynomialMap P 1)).obj
        (ModuleCat.of (affineAlgebra P 1) (affineForms P 1 i))) ≃ₗ[Construction61.crystallineCoverRing P]
      (ModuleCat.restrictScalars (affineBaseToPolynomialMap (Construction61.crystallineCover P) 1)).obj
        (ModuleCat.of (affineAlgebra (Construction61.crystallineCover P) 1)
          (affineForms (Construction61.crystallineCover P) 1 i)) :=
  (exists_affineOrientedFormsBaseChangeEquiv 1 i (Construction61.crystallineCoverMap P)
    (Construction61.crystallineCover_generator P)).choose

/-- 同じ元の単項式・外積基底の完備化単位を保つ。 -/
theorem affineCoverFormsEquiv_basis (P : OrientedPrism p A) (i : ℕ) (w) :
    affineCoverFormsEquiv P i
      ((1 : Construction61.crystallineCoverRing P) ⊗ₜ[A,(Construction61.crystallineCoverMap P).toRingHom]
        completedFormsUnit (A ⧸ P.ideal) (formVars.{u} 1) p i
          (polynomialFormsBasis (A ⧸ P.ideal) (formVars.{u} 1) i w)) =
      completedFormsUnit
        ((Construction61.crystallineCoverRing P) ⧸ (Construction61.crystallineCover P).ideal)
        (formVars.{u} 1) p i
        (polynomialFormsBasis
          ((Construction61.crystallineCoverRing P) ⧸ (Construction61.crystallineCover P).ideal)
          (formVars.{u} 1) i w) :=
  (exists_affineOrientedFormsBaseChangeEquiv 1 i (Construction61.crystallineCoverMap P)
    (Construction61.crystallineCover_generator P)).choose_spec w

/-- 元の指定e_targetのホモロジー同型。 -/
def affineOriginalCoverTargetHomologyIso
    (P : OrientedPrism p A) (hP : IsBoundedPrism P) (r : ℕ)
    (hF : IsCompletelyFlat (Ideal.span {Construction61.coverModPGenerator P})
      (baseChangeScalarModule (modPMap p P.deltaStructure.frobeniusLift)))
    (hR : IsSMulRegular (A ⧸ P.ideal) (p : A ⧸ P.ideal)) (i : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} (Construction61.crystallineCoverRing P)) (i : ℤ)).obj
      (DerivedCategory.Q.obj ((Construction61.completedCoverModelFunctor P).obj
        ((complexResolutionFunctor A).obj
          (affineComplexOnBase P r (affineHTTotalComplex P hP r))))) ≅
      (affineBaseComplex (Construction61.crystallineCover P)
        (Construction61.crystallineCover_bounded P) r).homology i :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} (Construction61.crystallineCoverRing P)) (i : ℤ)).mapIso
      (affineOriginalCoverTargetIso P hP r hF hR) ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} (Construction61.crystallineCoverRing P)) (i : ℤ)).app
      (affineComplexOnBase (Construction61.crystallineCover P) r
        (affineHTTotalComplex (Construction61.crystallineCover P) (Construction61.crystallineCover_bounded P) r)) ≪≫
    (homologyFunctor (ModuleCat.{u} (Construction61.crystallineCoverRing P)) (.up ℤ) (i : ℤ)).mapIso
      (affineOriginalBaseComplexIso (Construction61.crystallineCover P)
        (Construction61.crystallineCover_bounded P) r) ≪≫
    (affineBaseComplex (Construction61.crystallineCover P) (Construction61.crystallineCover_bounded P) r).extendHomologyIso
       ComplexShape.embeddingUpNat (j := i) (j' := (i : ℤ)) rfl

/-- 元の形式の係数同型と元の増大比較から得る零次の始域同型。 -/
def affineOriginalCoverSourceZeroIso (P : OrientedPrism p A) (hP : IsBoundedPrism P) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} (Construction61.crystallineCoverRing P)) 0).obj
      (DerivedCategory.Q.obj ((Construction61.completedCoverModelFunctor P).obj
        ((complexResolutionFunctor A).obj (affineComplexOnBase P 1 (affineLineFormalModel P))))) ≅
      (ModuleCat.restrictScalars (affineBaseToPolynomialMap (Construction61.crystallineCover P) 1)).obj
        (ModuleCat.of (affineAlgebra (Construction61.crystallineCover P) 1)
          (affineForms (Construction61.crystallineCover P) 1 0)) := by
  haveI := affineLineFormalCoverOrdinaryComparison_isIso P hP
  exact (DerivedCategory.homologyFunctor (ModuleCat.{u} (Construction61.crystallineCoverRing P)) 0).mapIso
      (asIso ((affineCoverOrdinaryComparison P 1).app (affineLineFormalModel P))) ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} (Construction61.crystallineCoverRing P)) 0).app
      ((affineOrdinaryCoverFunctor P 1).obj (affineLineFormalModel P)) ≪≫
    (affineLineFormalOrdinaryZeroIso P (Construction61.crystallineCoverMap P).toRingHom).symm ≪≫
    (affineCoverFormsEquiv P 0).toModuleIso

/-- 元の形式の係数同型と元の増大比較から得る一次の始域同型。 -/
def affineOriginalCoverSourceOneIso (P : OrientedPrism p A) (hP : IsBoundedPrism P) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} (Construction61.crystallineCoverRing P)) 1).obj
      (DerivedCategory.Q.obj ((Construction61.completedCoverModelFunctor P).obj
        ((complexResolutionFunctor A).obj (affineComplexOnBase P 1 (affineLineFormalModel P))))) ≅
      (ModuleCat.restrictScalars (affineBaseToPolynomialMap (Construction61.crystallineCover P) 1)).obj
        (ModuleCat.of (affineAlgebra (Construction61.crystallineCover P) 1)
          (affineForms (Construction61.crystallineCover P) 1 1)) := by
  haveI := affineLineFormalCoverOrdinaryComparison_isIso P hP
  exact (DerivedCategory.homologyFunctor (ModuleCat.{u} (Construction61.crystallineCoverRing P)) 1).mapIso
      (asIso ((affineCoverOrdinaryComparison P 1).app (affineLineFormalModel P))) ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} (Construction61.crystallineCoverRing P)) 1).app
      ((affineOrdinaryCoverFunctor P 1).obj (affineLineFormalModel P)) ≪≫
    (affineLineFormalOrdinaryOneIso P (Construction61.crystallineCoverMap P).toRingHom).symm ≪≫
    (affineCoverFormsEquiv P 1).toModuleIso

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
