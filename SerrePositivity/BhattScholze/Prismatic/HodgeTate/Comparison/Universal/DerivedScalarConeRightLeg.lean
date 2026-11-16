module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineReducedCone
public import SerrePositivity.HomologicalAlgebra.Complex.Cone
import all SerrePositivity.CommutativeAlgebra.Koszul.Basic

/-!
# 元の導来スカラー錐の右脚

## 概要
元の写像錐の右脚を、同じ局所化の比較を介して導来圏上の自然変換へ移す。

## 方針
複体の元の右脚の自然性と、元の局所化の自然変換の持ち上げを使う。

## 規約
代表ごとに任意の右脚を選ばず、元のmappingCone.inrを保つ。

## 使われ方
元の商の錐の指定同型と完備底変換の単位を、同じ右脚で照合する。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory HomologicalComplex
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R]

/-- 元の複体のスカラー錐の同じ右脚は、元の複体について自然。 -/
def scalarConeRightLeg (a : R) : 𝟭 (CochainComplex (ModuleCat.{u} R) ℤ) ⟶ scalarConeFunctor a where
  app K := CochainComplex.mappingCone.inr (smulId a K)
  naturality K L f := by
    apply HomologicalComplex.Hom.ext
    funext n
    change f.f n ≫ (CochainComplex.mappingCone.inr (smulId a L)).f n =
      (CochainComplex.mappingCone.inr (smulId a K)).f n ≫
        (cochainConeArrowMap _ _ (Arrow.homMk f f (by simp [smulId]))).f n
    exact (cochainConeArrowMap_inr (smulId a K) (smulId a L)
      (Arrow.homMk f f (by simp [smulId])) n).symm

/-- 元の右脚を同じ実局所化で写した自然変換。 -/
def scalarConeRightLegDerivedInput (a : R) :
    DerivedCategory.Q ⟶ scalarConeFunctor a ⋙ DerivedCategory.Q where
  app K := DerivedCategory.Q.map ((scalarConeRightLeg R a).app K)
  naturality K L f := by
    change DerivedCategory.Q.map f ≫ DerivedCategory.Q.map ((scalarConeRightLeg R a).app L) =
      DerivedCategory.Q.map ((scalarConeRightLeg R a).app K) ≫
        DerivedCategory.Q.map ((scalarConeFunctor a).map f)
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg DerivedCategory.Q.map ((scalarConeRightLeg R a).naturality f)

/-- 元の複体の右脚から降ろした、同じ導来スカラー錐の右脚。 -/
def derivedScalarConeRightLeg (a : R) :
    𝟭 (DerivedCategory (ModuleCat.{u} R)) ⟶ derivedScalarConeFunctor R a := by
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ))
      DerivedCategory.Q (𝟭 (DerivedCategory (ModuleCat.{u} R))) := ⟨Functor.rightUnitor _⟩
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ))
      (scalarConeFunctor a ⋙ DerivedCategory.Q) (derivedScalarConeFunctor R a) :=
    ⟨derivedScalarConeComparison R a⟩
  exact Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)) _ _ _ _
    (scalarConeRightLegDerivedInput R a)

/-- 元の導来右脚を代表の同じ写像錐へ戻すと、元の右脚そのものになる。 -/
@[reassoc] theorem derivedScalarConeRightLeg_comparison (a : R) (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (derivedScalarConeRightLeg R a).app (DerivedCategory.Q.obj K) ≫
        (derivedScalarConeComparison R a).hom.app K =
      DerivedCategory.Q.map (CochainComplex.mappingCone.inr (smulId a K)) := by
  simp [derivedScalarConeRightLeg, Localization.liftNatTrans_app,
    Localization.Lifting.iso, scalarConeRightLegDerivedInput, scalarConeRightLeg]

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
