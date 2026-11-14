module

public import SerrePositivity.CommutativeAlgebra.DividedPowers.Envelopes.PDLocalizationStructure
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Site.CrystallineSiteZariski
public import Mathlib.RingTheory.Localization.Away.Basic
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Site.CrystallineSiteBasic

/-!
# 結晶厚化の主開局所化

## 概要
厚化の台環を一元で局所化し、分冪・剰余構造射・p 冪零性を保つ。

## 方針
局所化した分冪を使い、局所化の分子と自然数の分母指数で濃度を評価する。

## 規約
濃度の上限は無限とする。結晶 cutoff の条件はこの仮定を供給する。

## 使われ方
Berthelot III.4、Stacks 07HN。Zariski 被覆の引き戻しと構造環の層性。
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory
open scoped Cardinal
namespace SerrePositivity.BhattScholze.Prismatic

/-- 結晶 cutoff の上限は可算濃度以上。 -/
theorem IsCrystallineCutoff.aleph0_le {k R : Type u} {κ : Cardinal.{u}}
    (hκ : IsCrystallineCutoff k R κ) : ℵ₀ ≤ κ := by
  have h : ℵ₀ ≤ Cardinal.mk k + Cardinal.mk R + ℵ₀ := self_le_add_left _ _
  exact h.trans ((Cardinal.self_le_power _ Cardinal.one_le_aleph0).trans hκ)

variable {p : ℕ} {k : Type u} [CommRing k] {J : Ideal k} {γ : DividedPowers J}
variable {R : Type u} [CommRing R] [Algebra (k ⧸ J) R] {κ : Cardinal.{u}}
variable (X : CrysOver p γ R κ) (b : X.B) (hκ : ℵ₀ ≤ κ)

include hκ in
/-- 主開局所化は無限の濃度の上限を保つ。 -/
theorem localizationAway_cardinal_le : Cardinal.mk (Localization.Away b) ≤ κ := by
  let L := Localization.Away b
  let f : X.B × ℕ → L := fun a => IsLocalization.mk' L a.1 (⟨b ^ a.2, ⟨a.2, rfl⟩⟩ : Submonoid.powers b)
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj b z
    refine ⟨(a, n), (IsLocalization.eq_mk'_iff_mul_eq.mpr ?_).symm⟩
    simpa only [map_pow] using ha
  apply (Cardinal.mk_le_of_surjective hf).trans
  simpa only [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_uzero,
    Cardinal.mk_nat, Cardinal.lift_aleph0] using
      (mul_le_mul' X.small hκ).trans (Cardinal.mul_eq_self hκ).le

/-- 主開局所化を実際の結晶厚化として読む。 -/
@[expose] def crysAway : CrysOver p γ R κ := by
  let L := Localization.Away b
  let : Algebra k L := ((algebraMap X.B L).comp (algebraMap k X.B)).toAlgebra
  exact {
    B := L
    JB := X.JB.map (algebraMap X.B L)
    δ := PDLocalizationDpow.localizationDividedPowers (Submonoid.powers b) L X.δ
    base_dp := by
      have hc : (algebraMap X.B L).comp (algebraMap k X.B) = algebraMap k L := rfl
      rw [← hc]
      exact (PDLocalizationDpow.localization_isDPMorphism (Submonoid.powers b) L X.δ).comp _ X.base_dp
    nilpotent := by
      simpa only [map_natCast] using X.nilpotent.map (algebraMap X.B L)
    sec := (Ideal.quotientMap _ (algebraMap X.B L) Ideal.le_comap_map).comp X.sec
    sec_comp := by
      ext a
      change (Ideal.quotientMap _ (algebraMap X.B L) Ideal.le_comap_map)
        (X.sec (algebraMap (k ⧸ J) R (Ideal.Quotient.mk J a))) = _
      rw [show X.sec (algebraMap (k ⧸ J) R (Ideal.Quotient.mk J a)) =
        Ideal.Quotient.mk X.JB (algebraMap k X.B a) from DFunLike.congr_fun X.sec_comp a]
      rfl
    small := localizationAway_cardinal_le X b hκ }

/-- 主開局所化の標準写像は厚化の射。 -/
@[expose] def crysAwayHom : X ⟶ crysAway X b hκ := by
  let L := Localization.Away b
  refine {
    toAlgHom := {
      toFun := algebraMap X.B L
      __ := algebraMap X.B L
      commutes' := fun _ => rfl }
    dp := PDLocalizationDpow.localization_isDPMorphism (Submonoid.powers b) L X.δ
    comm_sec := ?_ }
  intro r a ha
  change Ideal.Quotient.mk (X.JB.map (algebraMap X.B L)) (algebraMap X.B L a) =
    (Ideal.quotientMap _ (algebraMap X.B L) Ideal.le_comap_map) (X.sec r)
  rw [← ha]
  rfl

/-- 標準主開局所化の有限族は、単位イデアルを生成するとき Zariski 被覆となる。 -/
theorem crysAway_isZariskiFamily {ι : Type u} [Finite ι] (g : ι → X.B)
    (hg : Ideal.span (Set.range g) = ⊤) :
    CrysOver.IsZariskiFamily (fun i => crysAway X (g i) hκ)
      (fun i => crysAwayHom X (g i) hκ) := by
  refine ⟨g, hg, ?_⟩
  intro i
  refine ⟨?_, rfl⟩
  unfold IsLocalization.Away
  rw [isLocalization_iff_isLocalizationMap]
  change (Submonoid.powers (g i)).IsLocalizationMap
    (algebraMap X.B (Localization.Away (g i)))
  exact (isLocalization_iff_isLocalizationMap _ _).mp inferInstance

end SerrePositivity.BhattScholze.Prismatic
