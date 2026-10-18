module

public import SerrePositivity.KST.DerivedBlowup.PolynomialDerivedBaseChange
public import SerrePositivity.KST.DerivedBlowup.LiftedUniversalResolution

/-!
概要：KST Def3.1・Lemma3.6 の普遍基底上の実導来底変更を標準 Koszul チャートへ同定する。
方針：基底 K-flat 計算、多項式 pushout、標準チャート dg 底変更の Hom 同型を合成する。
規約：係数環の宇宙は任意。元の普遍基底は環同型 ULift で同じ宇宙へ移す。
使われ方：チャートの Koszul dg 模型の underlying 複体が実導来底変更を計算する根拠。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w w'

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory
attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {R : Type u} [CommRing R] {r : ℕ}

/-- 概要：普遍基底上での実際の導来底変更は標準 Koszul チャートの underlying 複体に同型。
方針：基底上の K-flat 比較と多項式 pushout 比較の後、dg 底変更関手の Hom 同型を合成する。
規約：KST Lemma3.6、係数環 R の平坦性は仮定しない。
使われ方：通常の普遍チャートの解消から任意基底の導来チャートへ進む局所計算。 -/
def liftedUniversalDerivedChartIso (a : Fin (r + 1) → R) (i : Fin (r + 1))
    [HasDerivedCategory.{w} (ModuleCat.{u} (LiftedUniversalBase.{u} r))]
    [HasDerivedCategory.{w'} (ModuleCat.{u} R)] :
    letI := (liftedUniversalSpecialization a).toAlgebra
    (DifferentialGraded.ScalarExtension.complexDerivedExtension
      (liftedUniversalSpecialization a)).obj
        (DerivedCategory.Q.obj (chartRestrictedExterior (liftedUniversalCoefficients.{u} r) i)) ≅
      DerivedCategory.Q.obj (chartRestrictedExterior a i) := by
  letI := (liftedUniversalSpecialization a).toAlgebra
  let K := chartExteriorCochain
    (fun j => MvPolynomial.C (liftedUniversalCoefficients.{u} r j))
    (chartCoordinate (LiftedUniversalBase.{u} r) i) i
  have := liftedUniversalChartBaseChangeDGFunctor_map_isIso a i
    ExteriorKoszulObject.point ExteriorKoszulObject.point
  let e := asIso ((liftedUniversalChartBaseChangeDGFunctor a i).map .point .point)
  exact polynomialDerivedBaseChangeIso (B := R) K
      (chartRestrictedExterior_kFlat (liftedUniversalCoefficients.{u} r) i) ≪≫
    DerivedCategory.Q.mapIso
      (((ModuleCat.restrictScalars (algebraMap R (ChartRing R i))).mapHomologicalComplex
        (.up ℤ)).mapIso e)

end SerrePositivity.KST.DerivedBlowup
