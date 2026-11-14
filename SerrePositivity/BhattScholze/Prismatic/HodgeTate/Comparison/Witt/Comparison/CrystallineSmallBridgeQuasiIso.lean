module
public meta import SerrePositivity.Util.Citation

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.CrystallineSmallBridgeComplex
public import SerrePositivity.HomologicalAlgebra.Cosimplicial.ScalarQuotient
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompleteScalarQuotient
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.CrystallineSmallBridgeComplex
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.CrystallineSmallBridge
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineSmallBridgeModP
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallinePDRetraction
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallinePDInclusion
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCompletedCech
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamCech
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateAffineModel
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.ModuleMap
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.ScalarQuotient
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.Quotient

/-!
# 小さい結晶の橋の整係数の擬同型

## 概要
結晶基底上の小さい結晶の橋は、基底線形な交代余面複体の擬同型を誘導する。

## 方針
実際の mod p の射を線形な複体へ移す。通常商の短完全列と両側の導来 p 完備性で
整係数へ持ち上げる。

## 規約
比較は既存の厳密な結晶の橋に対して述べる。

## 使われ方
BS 著者版 Theorem 6.4 の Witt の有限枠の比較への底変換。
-/

public noncomputable section

open CategoryTheory HomologicalComplex AlgebraicTopology SerrePositivity.Cosimplicial
open SerrePositivity.DerivedCompletion
open scoped Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic

set_option backward.isDefEq.respectTransparency false
attribute [local instance] HasDerivedCategory.standard

variable (p : ℕ) [Fact p.Prime] (r : ℕ)

private abbrev xBase := htBase (crystallineBasePrism.{u} p) (crystallineBaseBounded p) r
private abbrev yBase := pdCechBase p (crystallineBase.{u} p) r
private abbrev xD := htGenerator (crystallineBasePrism.{u} p) (crystallineBaseBounded p) r
private theorem xDNat {m n : SimplexCategory} (θ : m ⟶ n) :
    (zpCech.{u} p r).map θ (xD.{u} p r m) = xD.{u} p r n :=
  htGenerator_nat (crystallineBasePrism.{u} p) (crystallineBaseBounded p) r θ
private abbrev yD (n : SimplexCategory) : (pdRings.{u} p r).obj n := p
private theorem yDNat {m n : SimplexCategory} (θ : m ⟶ n) :
    (pdRings.{u} p r).map θ (yD.{u} p r m) = yD.{u} p r n :=
  map_natCast ((pdRings.{u} p r).map θ).hom p

private abbrev qX := quotProjection (zpCech.{u} p r) (xD.{u} p r) (xDNat.{u} p r) 1
private abbrev qY := quotProjection (pdRings.{u} p r) (yD.{u} p r) (yDNat.{u} p r) 1

private theorem quotient_base_comm :
    (xBase.{u} p r ≫ qX.{u} p r) ≫ crystallineSmallBridgeModP.{u} p r =
      yBase.{u} p r ≫ qY.{u} p r := by
  rw [crystallineSmallBridgeModP_eq_reduction]
  apply NatTrans.ext
  funext n
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change Ideal.Quotient.mk (Ideal.span {(p : (pdRings.{u} p r).obj n) ^ 1})
      ((crystallineSmallBridge.{u} p r).app n ((xBase.{u} p r).app n a)) = _
  exact congrArg (Ideal.Quotient.mk (Ideal.span {(p : (pdRings.{u} p r).obj n) ^ 1}))
    (ConcreteCategory.congr_hom (NatTrans.congr_app (smallBridge_base_comm.{u} p r) n) a)

private def quotientCochainMap :=
  moduleCochainMap (crystallineBase.{u} p) (xBase.{u} p r ≫ qX.{u} p r)
    (yBase.{u} p r ≫ qY.{u} p r) (crystallineSmallBridgeModP.{u} p r)
    (quotient_base_comm.{u} p r)

private theorem quotientCochainMap_quasiIso : QuasiIso (quotientCochainMap.{u} p r) :=
  moduleCochainMap_quasiIso_of_isCohomologyIso (crystallineBase.{u} p) _ _ _ _
    (crystallineSmallBridgeModP_isCohomologyIso.{u} p r)

private theorem x_base_scalar (n : SimplexCategory) :
    ((xBase.{u} p r).app n).hom (p : crystallineBase.{u} p) = xD.{u} p r n := by
  unfold xD htGenerator
  rw [crystallineBase_generator]

private theorem y_base_scalar (n : SimplexCategory) :
    ((yBase.{u} p r).app n).hom (p : crystallineBase.{u} p) = yD.{u} p r n :=
  map_natCast _ p

private theorem y_regular (n : SimplexCategory) :
    Function.Injective (fun x : (pdRings.{u} p r).obj n => yD.{u} p r n * x) := by
  obtain ⟨n⟩ := n
  intro x y h
  let e := CrystallinePDRetraction.termEquiv.{u} p r n
  apply e.injective
  apply CrystallinePDRetraction.regular.{u} p r n
  simpa only [map_mul, map_natCast] using congrArg e h

private abbrev projectionX := scalarQuotientCochainProjection (crystallineBase.{u} p)
  (zpCech.{u} p r) (xBase.{u} p r) (xD.{u} p r) (xDNat.{u} p r)
private abbrev projectionY := scalarQuotientCochainProjection (crystallineBase.{u} p)
  (pdRings.{u} p r) (yBase.{u} p r) (yD.{u} p r) (yDNat.{u} p r)

private theorem quotient_square :
    projectionX.{u} p r ≫ quotientCochainMap.{u} p r =
      crystallineSmallBridgeCochainMap.{u} p r ≫ projectionY.{u} p r := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (zpCech.{u} p r).obj ⦋i⦌ at x
  change (crystallineSmallBridgeModP.{u} p r).app ⦋i⦌ ((qX.{u} p r).app ⦋i⦌ x) =
    (qY.{u} p r).app ⦋i⦌ ((crystallineSmallBridge.{u} p r).app ⦋i⦌ x)
  rw [crystallineSmallBridgeModP_eq_reduction]
  rfl

/-- 小さい結晶の橋は整係数の線形な交代余面複体の擬同型を誘導する。 -/
theorem crystallineSmallBridgeCochainMap_quasiIso :
    QuasiIso (crystallineSmallBridgeCochainMap.{u} p r) := by
  let zX := scalarQuotientCochainProjection_zero (crystallineBase.{u} p)
    (zpCech.{u} p r) (xBase.{u} p r) (p : crystallineBase.{u} p)
    (xD.{u} p r) (xDNat.{u} p r) (x_base_scalar.{u} p r)
  let zY := scalarQuotientCochainProjection_zero (crystallineBase.{u} p)
    (pdRings.{u} p r) (yBase.{u} p r) (p : crystallineBase.{u} p)
    (yD.{u} p r) (yDNat.{u} p r) (y_base_scalar.{u} p r)
  have hX := scalarQuotientCochainProjection_shortExact (crystallineBase.{u} p)
    (zpCech.{u} p r) (xBase.{u} p r) (p : crystallineBase.{u} p)
    (xD.{u} p r) (xDNat.{u} p r) (x_base_scalar.{u} p r)
    (htGenerator_regular (crystallineBasePrism.{u} p) (crystallineBaseBounded p) r)
  have hY := scalarQuotientCochainProjection_shortExact (crystallineBase.{u} p)
    (pdRings.{u} p r) (yBase.{u} p r) (p : crystallineBase.{u} p)
    (yD.{u} p r) (yDNat.{u} p r) (y_base_scalar.{u} p r) (y_regular.{u} p r)
  exact cochainNat_quasiIso_of_complete_of_scalarQuotient (p : crystallineBase.{u} p)
    (crystallineSmallBridgeCochainMap.{u} p r) (projectionX.{u} p r) (projectionY.{u} p r)
    zX zY hX hY (quotientCochainMap.{u} p r) (quotient_square.{u} p r)
    (quotientCochainMap_quasiIso.{u} p r)
    (crystallineSmallSourceComplex_isComplete.{u} p r)
    (crystallineSmallTargetComplex_isComplete.{u} p r)

end SerrePositivity.BhattScholze.Prismatic

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Thm 5.2" (partial := component) "結晶の橋の mod p のコホモロジー同型（有限変数・I＝(p)）。比較同型そのものは D68 の段 3 と結晶サイト（a1-design §11） ／ 11-10 更新。整係数の版と W(C)・J の多項式の版（Thm 6.4 で使う形）も本体 ／ 11-12 夜更新（§5・§6 の見直し）"] _root_.SerrePositivity.BhattScholze.Prismatic.crystallineSmallBridgeCochainMap_quasiIso
