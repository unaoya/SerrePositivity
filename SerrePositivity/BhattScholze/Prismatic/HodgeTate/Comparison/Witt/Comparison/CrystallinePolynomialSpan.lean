module

public import Mathlib.CategoryTheory.Whiskering
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDSmallModelComparison
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamCech
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamCompletedColumnZero
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.CompletedCechCoefficientMap
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.CompletedCechCoefficientMap
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamCech
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCechNerve

/-!
# 多項式の結晶 Poincaré 比較の古典的な span

## 概要
実際の分冪 Čech 複体と完備 de Rham 複体を、総複体からの二射影で比較する。

## 方針
P1 の小さい模型との同型を第0行の比較に合成する。第0列への比較は P2 の射影を使う。

## 規約
基底は p 完備・p ねじれなし、分冪の p 上の条件を明示する。
RΓ や Tot の E∞ 構造は定義しない。

## 使われ方
BS 著者版 Theorem 6.4、Berthelot III.4、Stacks 07LG の多項式の複体比較。
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory AlgebraicTopology
namespace SerrePositivity.BhattScholze.Prismatic
variable (p : ℕ) [Fact p.Prime] (k : Type u) [CommRing k]
variable {J : Ideal k} (γ : DividedPowers J) (hp : (p : k) ∈ J)
variable (hγ : ∀ n : ℕ, (n.factorial : k) * γ.dpow n (p : k) = (p : k) ^ n)
variable (hk : IsAdicComplete (Ideal.span {(p : k)}) k)
variable (hreg : Function.Injective (fun x : k => (p : k) * x)) (r : ℕ)
variable (hJ : J ≤ RingHom.ker (algebraMap k (MvPolynomial (Fin r) (k ⧸ J))))
set_option quotPrecheck false
local notation "N" => pdCechNerve p γ hp hJ
  (fun j : ULift (Fin r) => (MvPolynomial.X j.down : MvPolynomial (Fin r) (k ⧸ J)))
local notation "Alt" => alternatingCofaceMapComplex (ModuleCat k)

/-- 第0行を、有限枠の実際の分冪 Čech 複体へ同定する。 -/
def crystallinePolynomialRowIso :
    (Alt).obj (pdRow p k r 0) ≅ (Alt).obj ((N) ⋙ PDCechNerve.algebraModule k) :=
  pdDeRhamRowZeroIso p k r ≪≫ (Alt).mapIso
    ((underCechModuleIso k (pdModel p k r)).symm ≪≫
      Functor.isoWhiskerRight (pdModel_iso_pdCechNerve p k γ hp hγ hk hreg r hJ)
        (PDCechNerve.algebraModule k))

/-- 総複体から実際の有限枠の分冪 Čech 複体への射影。 -/
def crystallinePolynomialTotalToCech :
    pdDeRhamTotal p k r ⟶ (Alt).obj ((N) ⋙ PDCechNerve.algebraModule k) :=
  pdDeRhamRowZeroProjection p k r ≫
    (crystallinePolynomialRowIso p k γ hp hγ hk hreg r hJ).hom

/-- 分冪 Čech 複体への射影は擬同型。もう一方の脚は既存の完備形式への射影。 -/
theorem crystallinePolynomialTotalToCech_quasiIso :
    QuasiIso (crystallinePolynomialTotalToCech p k γ hp hγ hk hreg r hJ) := by
  dsimp only [crystallinePolynomialTotalToCech]
  let := pdDeRhamRowZeroProjection_quasiIso p k r
  infer_instance

end SerrePositivity.BhattScholze.Prismatic
