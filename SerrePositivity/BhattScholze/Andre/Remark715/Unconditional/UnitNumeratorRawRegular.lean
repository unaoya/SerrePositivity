module

public import SerrePositivity.BhattScholze.Delta.Division.DeltaDivisionUniversal
public import SerrePositivity.BhattScholze.Delta.Extension.DeltaLocalization
public import Mathlib.RingTheory.Flat.Localization

/-!
# 分子に 1 を含む元の raw δ 包の p 正則性

## 概要
BS Rem 7.15（著者版 p.62）の次数零モニック入力では、元の raw 包も p 正則。

## 方針
除算関係から分母を単元にし、Frobenius 安定局所化へ写す実 δ 射の単射性を普遍性で示す。

## 規約
元の raw δ 閉包商を保つ。ねじれ除去・完備化は行わない。

## 使われ方
正次数入力の結果と合わせ、元の raw p 正則性から hpR を完全に除く。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze.Andre
set_option backward.isDefEq.respectTransparency false
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (d : A) (a : σ → A)
local notation "Raw" => DeltaAdjoinDivision D d a
local notation "j" => deltaAdjoinDivisionMap D d a
local notation "DRaw" => deltaAdjoinDivisionStructure D d a

/-- 概要：分子族に 1 があれば、元の raw 包で分母の標準像は単元。
方針：元の除算変数を逆元として使う。
規約：分母の正則性や p 正則性は不要。
使われ方：BS Rem 7.15（著者版 p.62）の次数零入力。 -/
theorem unconditionalRaw_denominator_isUnit_of_unit_numerator (ha : ∃ s, a s = 1) :
    IsUnit (j d) := by
  obtain ⟨s, hs⟩ := ha
  have hv : j d * deltaAdjoinDivisionVariable D d a s = 1 := by
    rw [deltaAdjoinDivision_relation, hs, map_one]
  exact ⟨⟨j d, deltaAdjoinDivisionVariable D d a s, hv, (mul_comm _ _).trans hv⟩, rfl⟩

/-- 概要：分子族に 1 があれば、元の raw 包の p 正則性は係数環から従う。
方針：実安定局所化への δ 射に左逆を作り、局所化の p 正則性を元の raw 包へ戻す。
規約：prism 商の正則性を要求せず、元の raw 包を保つ。
使われ方：BS Rem 7.15（著者版 p.62）の次数零モニック入力の p 正則性。 -/
theorem unconditionalRaw_prime_regular_of_unit_numerator
    (hp : IsSMulRegular A (p : A)) (ha : ∃ s, a s = 1) :
    IsSMulRegular Raw (p : Raw) := by
  let T := D.frobeniusDenominators (Submonoid.powers d)
  let B := Localization T
  let DB := D.localization T B (D.frobeniusDenominators_stable (Submonoid.powers d))
  have hdB : IsUnit (algebraMap A B d) := IsLocalization.map_units B
    ⟨d, D.le_frobeniusDenominators (Submonoid.powers d) (Submonoid.mem_powers d)⟩
  have hdRaw := unconditionalRaw_denominator_isUnit_of_unit_numerator D d a ha
  have hj : D.IsDeltaHom DRaw j := deltaAdjoinDivisionMap_isDeltaHom D d a
  obtain ⟨f, hf, _⟩ := existsUnique_deltaAdjoinDivisionHom_of_regular D DB d a
    (algebraMap A B)
    (D.isDeltaHom_localization T B (D.frobeniusDenominators_stable (Submonoid.powers d)))
    hdB.mul_right_injective (fun s => hdB.dvd)
  have hM (s : Submonoid.powers d) : IsUnit (j s) := by
    obtain ⟨n, hn⟩ := s.property
    rw [← hn, map_pow]
    exact hdRaw.pow n
  obtain ⟨g, hg, _⟩ := D.existsUnique_saturatedLocalization_lift (Submonoid.powers d)
    B DRaw j hj hM
  obtain ⟨_, _, hu⟩ := existsUnique_deltaAdjoinDivisionHom_of_regular D DRaw d a j hj
    hdRaw.mul_right_injective (fun s => hdRaw.dvd)
  have hbase : (g.comp f).comp j = j := by
    rw [RingHom.comp_assoc, hf.2, hg.1]
  have hgf : g.comp f = RingHom.id Raw :=
    (hu _ ⟨hg.2.comp hf.1, hbase⟩).trans
      (hu _ ⟨fun _ => rfl, RingHom.id_comp j⟩).symm
  have hfi : Function.Injective f :=
    (show Function.LeftInverse g f from fun x => DFunLike.congr_fun hgf x).injective
  letI : Module.Flat A B := IsLocalization.flat B T
  have hpB : IsSMulRegular B (p : B) := by
    simpa only [map_natCast] using hp.of_flat (S := B)
  intro x y hxy
  apply hfi
  apply hpB
  change (p : B) * f x = (p : B) * f y
  simpa only [smul_eq_mul, map_mul, map_natCast] using congrArg f hxy

end SerrePositivity.BhattScholze.Andre
