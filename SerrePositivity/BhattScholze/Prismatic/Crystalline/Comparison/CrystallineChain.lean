module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamCohomology
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.PDModelReduction
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineBridgePushout
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateZero

/-!
# 結晶基底での加法的 de Rham 比較

## 概要
affine Hodge–Tate コホモロジーから多項式 de Rham コホモロジーへの加法同型。

## 方針
結晶の橋、余分な座標を加える包含の逆、分冪模型の mod p と総複体の比較を合成する。

## 規約
結晶基底は ℤ_p。多項式の変数を係数環の宇宙へ持ち上げる。

## 使われ方
Cartier 同型との生成元の照合。
-/

public noncomputable section

open CategoryTheory SerrePositivity.Cosimplicial SerrePositivity.DeRham

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable (p : ℕ) [Fact p.Prime]

/-- 結晶基底での多項式 de Rham 複体。 -/
abbrev crystallinePolynomialDeRham (r : ℕ) :=
  deRhamComplex (cartierBase.{u} p) (formVars.{u} r)

/-- 結晶基底の affine 模型と多項式 de Rham 複体のコホモロジーの加法同型。 -/
def crystallineChain (r i : ℕ) :
    hodgeTateCohomology' (crystallineBasePrism.{u} p) (crystallineBaseBounded p) r i ≃+
      (crystallinePolynomialDeRham.{u} p r).homology i :=
  ((crystallineBridgeModP_isCohomologyIso p r).addEquiv i).trans
    ((((pdInclusionModP_isCohomologyIso p r).addEquiv i).symm.trans
      ((isCohomologyIso_of_isIso (pdModel_modP p r).hom).addEquiv i)).trans
      (pdDeRhamCechToPolynomial p (cartierBase.{u} p) r (cartierBase_natCast p) i))

end SerrePositivity.BhattScholze.Prismatic
