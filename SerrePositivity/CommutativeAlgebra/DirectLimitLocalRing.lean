module

public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! # 有向直極限の局所性

局所環の有向直極限の局所性、局所な遷移写像からの局所な標準写像、
基底の極大イデアルの拡張の保存を証明する。Noether性は要求しない。
-/

public section
namespace SerrePositivity
open IsLocalRing
variable {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
variable (S : ι → Type*) [∀ i, CommRing (S i)]
variable {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*}
variable [∀ i j (h : i ≤ j), FunLike (T h) (S i) (S j)]
variable [∀ i j (h : i ≤ j), RingHomClass (T h) (S i) (S j)]
variable (f : ∀ i j (h : i ≤ j), T h) [DirectedSystem S (f · · ·)]

/-- 直極限で単元になる元は、ある後続段で既に単元になる。 -/
theorem directLimit_isUnit_iff (i : ι) (x : S i) :
    IsUnit (DirectLimit.Ring.of S f i x) ↔ ∃ j, ∃ h : i ≤ j, IsUnit (f i j h x) := by
  constructor
  · intro hx
    obtain ⟨y, hxy⟩ := isUnit_iff_exists_inv.mp hx
    obtain ⟨k, z, hz⟩ := DirectLimit.exists_eq_mk f y
    rw [hz] at hxy
    obtain ⟨j, hij, hkj⟩ := exists_ge_ge i k
    have hm : DirectLimit.Ring.of S f j (f i j hij x * f k j hkj z) = 1 := by
      rw [map_mul, DirectLimit.Ring.of_f, DirectLimit.Ring.of_f]
      exact hxy
    obtain ⟨l, hjl, hl⟩ := (DirectLimit.exists_eq_one (f := f)
      ⟨j, f i j hij x * f k j hkj z⟩).mp hm
    refine ⟨l, hij.trans hjl, isUnit_iff_exists_inv.mpr ⟨f j l hjl (f k j hkj z), ?_⟩⟩
    simpa only [map_mul, DirectedSystem.map_map'] using hl
  · rintro ⟨j, hij, hx⟩
    rw [← DirectLimit.Ring.of_f (G := S) (f := f) hij x]
    exact hx.map (DirectLimit.Ring.of S f j)

/-- 局所環の非空有向直極限は局所環である。遷移写像の局所性は不要。 -/
theorem directLimit_isLocalRing [∀ i, IsLocalRing (S i)] :
    IsLocalRing (DirectLimit S f) := by
  refine ⟨fun {x y} h ↦ ?_⟩
  obtain ⟨i, a, b, ha, hb⟩ := DirectLimit.exists_eq_mk₂ f x y
  have ha' : DirectLimit.Ring.of S f i a = x := by with_unfolding_all exact ha.symm
  have hb' : DirectLimit.Ring.of S f i b = y := by with_unfolding_all exact hb.symm
  have hab : DirectLimit.Ring.of S f i (a + b) = 1 := by
    rw [map_add, ha', hb']
    exact h
  obtain ⟨j, hij, hj⟩ := (DirectLimit.exists_eq_one (f := f) ⟨i, a + b⟩).mp hab
  have hu := IsLocalRing.isUnit_or_isUnit_of_add_one (by simpa only [map_add] using hj)
  exact hu.imp (fun hunit ↦ ha' ▸ (directLimit_isUnit_iff S f i a).mpr ⟨j, hij, hunit⟩)
    (fun hunit ↦ hb' ▸ (directLimit_isUnit_iff S f i b).mpr ⟨j, hij, hunit⟩)

/-- 遷移写像が局所なら、各段から直極限への標準写像も局所である。 -/
theorem directLimit_isLocalHom
    (hlocal : ∀ i j h, IsLocalHom (RingHomClass.toRingHom (f i j h))) (i : ι) :
    IsLocalHom (DirectLimit.Ring.of S f i) := by
  refine ⟨fun x hx ↦ ?_⟩
  obtain ⟨j, hij, hj⟩ := (directLimit_isUnit_iff S f i x).mp hx
  let : IsLocalHom (RingHomClass.toRingHom (f i j hij)) := hlocal i j hij
  exact isUnit_of_map_unit (RingHomClass.toRingHom (f i j hij)) x hj

end SerrePositivity
