module

public import SerrePositivity.BhattScholze.Prismatic.CompletedPDEnvelopeCardinality
public import SerrePositivity.BhattScholze.Prismatic.PDCechCrystallineTower
public import SerrePositivity.CategoryTheory.ProCechNerveTransport
import all SerrePositivity.BhattScholze.Prismatic.CrystallineCechProWeakTerminal
import all SerrePositivity.BhattScholze.Prismatic.PDCechCrystallineTower
import all Mathlib.CategoryTheory.Opposites

/-!
# cutoff の中の結晶 pd Čech の塔

## 概要
包の濃度を個別に仮定せず、枠と cutoff の上限から結晶サイト内の塔を構成する。

## 方針
全項の濃度評価を、既存の塔・pro 弱終性・各段の Čech データへ供給する。

## 規約
枠の変数を #k+#R+ℵ₀ で抑える。標準の枠 S=R と有限多項式枠はこの条件を満たす。

## 使われ方
BS 著者版 Theorem 5.2、Berthelot III.4、Stacks 07HP。小さい結晶サイトの pro Čech 計算の古典入力。
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory
open scoped Cardinal
namespace SerrePositivity.BhattScholze.Prismatic
variable (p : ℕ) {k : Type u} [CommRing k] {J : Ideal k} (γ : DividedPowers J)
variable (hp : (p : k) ∈ J) (R : Type u) [CommRing R] [Algebra (k ⧸ J) R]
variable [Algebra k R] [IsScalarTower k (k ⧸ J) R]
variable {S : Type u} (s : S → R) (hs : Function.Surjective (pdFrameEval (k := k) s 0))
variable {κ : Cardinal.{u}}

/-- cutoff から全 Čech 項の濃度条件を得る。 -/
theorem pdCechCutoffBound (hS : Cardinal.mk S ≤ Cardinal.mk k + Cardinal.mk R + ℵ₀)
    (hκ : IsCrystallineCutoff k R κ) (n : ℕ) : Cardinal.mk
      (PDCechNerve.term p γ hp (crysResidue_kernel_of_tower (J := J) R) s n).carrier ≤ κ :=
  pdCechTerm_cardinal_le_of_cutoff p γ hp (crysResidue_kernel_of_tower (J := J) R) s hS hκ n

/-- 包の濃度仮定を cutoff から供給した、環の向きの pd Čech の塔。 -/
def pdCechTowerOfCutoff (hS : Cardinal.mk S ≤ Cardinal.mk k + Cardinal.mk R + ℵ₀)
    (hκ : IsCrystallineCutoff k R κ) : ℕᵒᵖ × SimplexCategory ⥤ CrysOver p γ R κ :=
  pdCechTower p γ hp R s hs (pdCechCutoffBound p γ hp R s hS hκ)

/-- cutoff の中の零次の塔を、小さい結晶サイトの向きで読む。 -/
def pdCechSmallTowerOfCutoff (hS : Cardinal.mk S ≤ Cardinal.mk k + Cardinal.mk R + ℵ₀)
    (hκ : IsCrystallineCutoff k R κ) : ℕ ⥤ CrystallineSite p γ R κ :=
  pdCechSmallTowerZero p γ hp R s hs (pdCechCutoffBound p γ hp R s hS hκ 0)

/-- cutoff の中の小さいサイトでの、各段の Čech データと射影を保つ遷移。 -/
def pdCechProCechDataOfCutoff (hS : Cardinal.mk S ≤ Cardinal.mk k + Cardinal.mk R + ℵ₀)
    (hκ : IsCrystallineCutoff k R κ) :
    ProCechNerveData (pdCechSmallTowerOfCutoff p γ hp R s hs hS hκ) :=
  (pdCechTowerProCechData p γ hp R s hs (pdCechCutoffBound p γ hp R s hS hκ)).mapEquivalence
    (equivSmallModel (CrysOver p γ R κ)).op

/-- 包の濃度を個別に仮定せず、小さい結晶サイトの塔の pro 弱終性を得る。 -/
theorem pdCechSmallTowerOfCutoff_proWeaklyTerminal
    (hS : Cardinal.mk S ≤ Cardinal.mk k + Cardinal.mk R + ℵ₀)
    (hκ : IsCrystallineCutoff k R κ) :
    IsProWeaklyTerminal (pdCechSmallTowerOfCutoff p γ hp R s hs hS hκ) :=
  pdCechSmallTowerZero_proWeaklyTerminal p γ hp R s hs (pdCechCutoffBound p γ hp R s hS hκ 0)

end SerrePositivity.BhattScholze.Prismatic
