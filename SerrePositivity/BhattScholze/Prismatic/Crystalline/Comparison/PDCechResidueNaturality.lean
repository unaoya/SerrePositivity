module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCechCrystallineQuotient
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCechCrystallineQuotient
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCechNerve

/-!
# 分冪 Čech 包の剰余構造射の自然性

## 概要
頂点の任意の写像による分冪射が、剰余同型とその逆の構造射を保つ。

## 方針
商の代表元で既存の増強の自然性へ帰着する。

## 規約
単体射に限定せず、頂点集合の任意の写像について述べる。

## 使われ方
Berthelot III.4、Stacks 07HP。結晶サイトの pd Čech の単体構造。
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.BhattScholze.Prismatic
variable (p : ℕ) {k : Type u} [CommRing k] {J : Ideal k} (γ : DividedPowers J)
variable (hp : (p : k) ∈ J) (R : Type u) [CommRing R] [Algebra (k ⧸ J) R]
variable [Algebra k R] [IsScalarTower k (k ⧸ J) R]
local notation "hJ" => crysResidue_kernel_of_tower (J := J) R
variable {S : Type u} (s : S → R) (hs : Function.Surjective (pdFrameEval (k := k) s 0))
local notation "D" n => PDCechNerve.term p γ hp hJ s n
local notation "E" n => crystallineCechResidueEquiv p γ hp hJ s hs n

/-- 頂点の写像が誘導する分冪剰余環の射。 -/
def pdCechResidueMap {m n : ℕ} (θ : Fin (m + 1) → Fin (n + 1)) :
    ((D m).carrier ⧸ (D m).ideal) →+* ((D n).carrier ⧸ (D n).ideal) :=
  Ideal.quotientMap _ (PDCechNerve.mapCopies p γ hp hJ s θ).toRingHom
    (Ideal.map_le_iff_le_comap.mp (PDCechNerve.mapCopies_isDPMorphism p γ hp hJ s θ).ideal_comp)

/-- 分冪剰余環の射は、剰余同型のもとで恒等射になる。 -/
theorem pdCechResidueMap_equiv {m n : ℕ} (θ : Fin (m + 1) → Fin (n + 1)) :
    (E n).toRingHom.comp (pdCechResidueMap p γ hp R s θ) = (E m).toRingHom := by
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro b
  change (E n) (Ideal.Quotient.mk _ (PDCechNerve.mapCopies p γ hp hJ s θ b)) =
    (E m) (Ideal.Quotient.mk _ b)
  rw [crystallineCechResidueEquiv_mk, crystallineCechResidueEquiv_mk,
    PDCechNerve.augmentation_mapCopies]

/-- 頂点の写像による分冪射は、元の剰余代数からの構造射と可換。 -/
theorem pdCechResidueMap_section {m n : ℕ} (θ : Fin (m + 1) → Fin (n + 1)) :
    (pdCechResidueMap p γ hp R s θ).comp (pdCechResidueSection p γ hp R s hs m) =
      pdCechResidueSection p γ hp R s hs n := by
  ext r
  apply (E n).injective
  have h := DFunLike.congr_fun (pdCechResidueMap_equiv p γ hp R s hs θ)
    ((E m).symm r)
  change (E n) (pdCechResidueMap p γ hp R s θ ((E m).symm r)) =
    (E n) ((E n).symm r)
  exact h.trans ((E m).apply_symm_apply r) |>.trans ((E n).apply_symm_apply r).symm

end SerrePositivity.BhattScholze.Prismatic
