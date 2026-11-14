module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineChain
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamCohomologyProduct
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineChain
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.Cohomology

/-!
# 結晶基底での de Rham 比較の積

## 概要
結晶基底での比較は affine 模型の cup 積を de Rham コホモロジーの外積に移す。

## 方針
余単体的環の射から得たコホモロジー同型とその逆の乗法性を合成する。

## 規約
最後の比較は pd de Rham 総複体の二つの射影で与える。

## 使われ方
Cartier 同型との Hodge–Tate 生成元での照合。
-/

public noncomputable section

open CategoryTheory SerrePositivity.Cosimplicial SerrePositivity.DeRham

universe u

namespace SerrePositivity.Cosimplicial

private theorem cohomologyIso_cup {X Y : CosimplicialObject CommRingCat.{u}} {f : X ⟶ Y}
    (e : IsCohomologyIso f) {i j : ℕ} (a : cohomology X i) (b : cohomology X j) :
    e.addEquiv (i+j) (cohomologyCup X a b) =
      cohomologyCup Y (e.addEquiv i a) (e.addEquiv j b) :=
  cohomologyMap_cup X Y f a b

private theorem cohomologyIso_symm_cup {X Y : CosimplicialObject CommRingCat.{u}} {f : X ⟶ Y}
    (e : IsCohomologyIso f) {i j : ℕ} (a : cohomology Y i) (b : cohomology Y j) :
    (e.addEquiv (i+j)).symm (cohomologyCup Y a b) =
      cohomologyCup X ((e.addEquiv i).symm a) ((e.addEquiv j).symm b) := by
  apply (e.addEquiv (i+j)).injective
  rw [AddEquiv.apply_symm_apply, cohomologyIso_cup, AddEquiv.apply_symm_apply,
    AddEquiv.apply_symm_apply]

end SerrePositivity.Cosimplicial

namespace SerrePositivity.BhattScholze.Prismatic

variable (p : ℕ) [Fact p.Prime]

set_option backward.isDefEq.respectTransparency false in
/-- 結晶の比較は cup 積と外積に両立する。 -/
theorem crystallineChain_cup (r : ℕ) {i j : ℕ}
    (a : hodgeTateCohomology' (crystallineBasePrism.{u} p) (crystallineBaseBounded p) r i)
    (b : hodgeTateCohomology' (crystallineBasePrism.{u} p) (crystallineBaseBounded p) r j) :
    crystallineChain p r (i+j) (cohomologyCup _ a b) =
      deRhamCohomologyWedge _ _ (crystallineChain p r i a) (crystallineChain p r j b) := by
  let f := crystallineBridgeModP_isCohomologyIso p r
  let g := pdInclusionModP_isCohomologyIso p r
  let e := isCohomologyIso_of_isIso (pdModel_modP p r).hom
  let w := pdDeRhamCechToPolynomial p (cartierBase p) r (cartierBase_natCast p)
  change w (i+j) (e.addEquiv (i+j) ((g.addEquiv (i+j)).symm (f.addEquiv (i+j) (cohomologyCup _ a b)))) =
    deRhamCohomologyWedge _ _
      (w i (e.addEquiv i ((g.addEquiv i).symm (f.addEquiv i a))))
      (w j (e.addEquiv j ((g.addEquiv j).symm (f.addEquiv j b))))
  rw [cohomologyIso_cup f, cohomologyIso_symm_cup g, cohomologyIso_cup e]
  exact pdDeRhamCechToPolynomial_cup p (cartierBase p) r (cartierBase_natCast p) _ _

end SerrePositivity.BhattScholze.Prismatic
