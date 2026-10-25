module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.RestrictionKoszulStage
public import SerrePositivity.HomologicalAlgebra.DerivedRestriction
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.DerivedKoszulReduction

/-!
# 元のスカラー錐と係数制限

## 概要
BS Rem 7.15（著者版 p.62）の元の源の p 錐の冪ねじれ性を、元の基底作用へ移す。

## 方針
任意の実複体モデル上の係数制限とスカラー錐の比較を導来圏へ運ぶ。

## 規約
環射の平坦性・単射性を要求しない。

## 使われ方
自由 δ 源上の局所化計算と、元の prism 基底上の完備化純性を合流する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits DerivedCompletion
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] HasDerivedCategory.standard
variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)

/-- 概要：元の実スカラー錐と正確な係数制限は可換。
方針：同じ実複体モデル上の標準写像錐比較を使う。
規約：元のスカラーの像を保持する。
使われ方：BS Rem 7.15（著者版 p.62）の源の p 錐の標準基底作用。 -/
def unconditionalRestrictionScalarConeIso (a : R) (X : ConcreteDerivedCategory S) :
    (derivedScalarConeFunctor R a).obj ((derivedRestrictScalars φ).obj X) ≅
      (derivedRestrictScalars φ).obj ((derivedScalarConeFunctor S (φ a)).obj X) := by
  let K := DerivedCategory.Q.objPreimage X
  let eX := DerivedCategory.Q.objObjPreimageIso X
  let KR := ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj K
  exact (derivedScalarConeFunctor R a).mapIso
      ((derivedRestrictScalars φ).mapIso eX.symm ≪≫ (derivedRestrictScalarsFactors φ).app K) ≪≫
    (derivedScalarConeComparison R a).app KR ≪≫
    DerivedCategory.Q.mapIso (restrictionScalarConeIso φ a (φ a) rfl K).symm ≪≫
    ((derivedRestrictScalarsFactors φ).app ((scalarConeFunctor (φ a)).obj K)).symm ≪≫
    (derivedRestrictScalars φ).mapIso
      ((derivedScalarConeComparison S (φ a)).symm.app K ≪≫
        (derivedScalarConeFunctor S (φ a)).mapIso eX)

/-- 概要：元の実スカラー錐の冪ねじれ性は、同じ基底元の係数制限へ移る。
方針：実錐比較とホモロジー係数制限の線形同型を使う。
規約：指数は元ごとに異なってよい。
使われ方：BS Rem 7.15（著者版 p.62）の局所化計算の元の A 作用への移送。 -/
theorem unconditionalRestrictionScalarCone_homology_power_torsion
    (a d : R) (X : ConcreteDerivedCategory S) (i : ℤ)
    (ht : ∀ x : (DerivedCategory.homologyFunctor (ModuleCat S) i).obj
      ((derivedScalarConeFunctor S (φ a)).obj X), ∃ n : ℕ, (φ d) ^ n • x = 0)
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) i).obj
      ((derivedScalarConeFunctor R a).obj ((derivedRestrictScalars φ).obj X))) :
    ∃ n : ℕ, d ^ n • x = 0 := by
  let e := (DerivedCategory.homologyFunctor (ModuleCat R) i).mapIso
      (unconditionalRestrictionScalarConeIso φ a X) ≪≫
    (derivedRestrictScalarsHomologyIso φ i).app ((derivedScalarConeFunctor S (φ a)).obj X)
  let y : (DerivedCategory.homologyFunctor (ModuleCat S) i).obj
    ((derivedScalarConeFunctor S (φ a)).obj X) := e.hom x
  obtain ⟨n, hn⟩ := ht y
  refine ⟨n, e.toLinearEquiv.injective ?_⟩
  rw [e.toLinearEquiv.map_smul, e.toLinearEquiv.map_zero]
  change φ (d ^ n) • y = 0
  rw [map_pow]
  exact hn

/-- 概要：同じ冪ねじれの移送を、元の上に有界な係数制限対象で述べる。
方針：標準の包含比較と実ホモロジー同型で前の判定を移す。
規約：元の boundedAboveDerivedRestrictScalars を保持する。
使われ方：BS Rem 7.15（著者版 p.62）の具体的な実源の型の照合。 -/
theorem unconditionalBoundedRestrictionScalarCone_homology_power_torsion
    (a d : R) (X : DerivedCategory.Minus (ModuleCat.{u} S)) (i : ℤ)
    (ht : ∀ x : (DerivedCategory.homologyFunctor (ModuleCat S) i).obj
      ((derivedScalarConeFunctor S (φ a)).obj X.obj), ∃ n : ℕ, (φ d) ^ n • x = 0)
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) i).obj
      ((derivedScalarConeFunctor R a).obj ((boundedAboveDerivedRestrictScalars φ).obj X).obj)) :
    ∃ n : ℕ, d ^ n • x = 0 := by
  let eI := (boundedAboveDerivedRestrictScalarsInclusionIso φ).app X
  let eH := (DerivedCategory.homologyFunctor (ModuleCat R) i).mapIso
    ((derivedScalarConeFunctor R a).mapIso eI)
  obtain ⟨n, hn⟩ := unconditionalRestrictionScalarCone_homology_power_torsion
    φ a d X.obj i ht (eH.hom x)
  refine ⟨n, eH.toLinearEquiv.injective ?_⟩
  rw [eH.toLinearEquiv.map_smul, eH.toLinearEquiv.map_zero]
  exact hn

end SerrePositivity.BhattScholze.Andre
