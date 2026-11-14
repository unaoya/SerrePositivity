module

public import SerrePositivity.BhattScholze.Prismatic.Envelopes.CompletedFreeDelta

/-!
# 完備自由 δ 環の単元による座標の変更

## 概要
選んだ初期座標を係数環の単元倍に変えると、基底上の δ 環の自己同型になる。

## 方針
完備自由 δ 環の普遍性で両向きの射を作り、初期座標で逆写像の等式を確かめる。

## 規約
座標の集合は任意。単元の像は基底の構造射で読む。

## 使われ方
BS 著者版 Proposition 3.13 (2) と Theorem 6.4 の affine 包の底変換で、
基底の生成元の単元倍による違いを分母の座標に移す。
-/

public noncomputable section

attribute [local instance] Classical.propDecidable

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (P : OrientedPrism p A) (S : Type u) (Z : Set S)

local notation "C" => completedFreeDelta P S
local notation "D" => completedFreeDeltaStructure P S
local notation "b" => completedFreeDeltaBase P S
local notation "X" => completedFreeDeltaVariable P S

private def value (a : Aˣ) (s : S) : C := by
  classical
  exact if s ∈ Z then b a * X s else X s

private theorem existsUnique_scale (a : Aˣ) :
    ∃! g : C →+* C, (D).IsDeltaHom D g ∧ g.comp b = b ∧
      ∀ s, g (X s) = value P S Z a s :=
  existsUnique_completedFreeDeltaHom P S D b (completedFreeDeltaBase_isDeltaHom P S)
    (completedFreeDelta_complete_p P S) (completedFreeDelta_complete_generator P S)
    (value P S Z a)

private def scale (a : Aˣ) : C →+* C := (existsUnique_scale P S Z a).choose

private theorem scale_spec (a : Aˣ) :
    (D).IsDeltaHom D (scale P S Z a) ∧ (scale P S Z a).comp b = b ∧
      ∀ s, scale P S Z a (X s) = value P S Z a s :=
  (existsUnique_scale P S Z a).choose_spec.1

private theorem scale_inverse (a : Aˣ) :
    (scale P S Z a⁻¹).comp (scale P S Z a) = RingHom.id C := by
  classical
  have ha := scale_spec P S Z a
  have hb := scale_spec P S Z a⁻¹
  apply completedFreeDeltaHom_ext P S D b (completedFreeDeltaBase_isDeltaHom P S)
    (completedFreeDelta_complete_p P S) (completedFreeDelta_complete_generator P S)
    (hb.1.comp ha.1) (D).isDeltaHom_id
  · rw [RingHom.comp_assoc, ha.2.1, hb.2.1]
  · exact RingHom.id_comp _
  · intro s
    change scale P S Z a⁻¹ (scale P S Z a (X s)) = X s
    rw [ha.2.2]
    by_cases hs : s ∈ Z
    · simp only [value, hs, ite_true, map_mul]
      have hbase (x : A) : scale P S Z a⁻¹ (b x) = b x :=
        RingHom.congr_fun hb.2.1 x
      rw [hbase, hb.2.2]
      simp only [value, hs, ite_true, ← mul_assoc, ← map_mul, Units.mul_inv, map_one,
        one_mul]
    · simpa only [value, hs, ite_false] using hb.2.2 s

/-- 単元倍の座標変更は、基底と δ 構造を保つ自己同型。 -/
theorem exists_completedFreeDeltaScaleEquiv (a : Aˣ) :
    ∃ e : C ≃+* C, (D).IsDeltaHom D e.toRingHom ∧ e.toRingHom.comp b = b ∧
      ∀ s, e (X s) = if s ∈ Z then b a * X s else X s := by
  classical
  let e := RingEquiv.ofRingHom (scale P S Z a) (scale P S Z a⁻¹)
    (by simpa only [inv_inv] using scale_inverse P S Z a⁻¹)
    (scale_inverse P S Z a)
  exact ⟨e, (scale_spec P S Z a).1, (scale_spec P S Z a).2.1,
    (scale_spec P S Z a).2.2⟩

end SerrePositivity.BhattScholze.Prismatic
