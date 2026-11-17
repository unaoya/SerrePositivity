module

public import SerrePositivity.AlgebraicGeometry.PerfectAffineVCoverCech

/-!
概要：有限表示模型に用いる実際のFrobenius順極限の完全性と、完全な値域への延長。
方針：有限段の零判定で単射性、一段後の元でp乗根を示し、H01の自然な同型を合成する。
規約：p=0のみを要求して零環を保つ。Mathlibの逆極限Perfectionへ置き換えない。
使われ方：2iのM01〜M04・I00・P00、BM18 Proposition 4.8の模型の完全化。
-/

@[expose] public noncomputable section
universe u
open SerrePositivity
namespace SerrePositivity.AlgebraicGeometry.ArcRouteB

/-- 計画M01：同じFrobenius順極限・構造射を保つ完全環の入口。 -/
theorem frobeniusDirectLimit_primeCast_eq_zero
    (p : ℕ) (hp : p.Prime) (A : Type u) [CommRing A] (hA : (p : A) = 0) :
    (p : FrobeniusDirectLimit A p hp hA) = 0 := by
  rw [← map_natCast (frobeniusDirectLimitOf A p hp hA 0), hA, map_zero]

/-- 計画M02：同じFrobenius順極限・構造射を保つ完全環の入口。 -/
theorem frobeniusDirectLimit_perfectRing
    (p : ℕ) [Fact p.Prime] (A : Type u) [CommRing A] (hA : (p : A) = 0) :
    PerfectRing (FrobeniusDirectLimit A p (Fact.out : p.Prime) hA) p := by
  let hp : p.Prime := Fact.out
  let hL : (p : FrobeniusDirectLimit A p hp hA) = 0 :=
    frobeniusDirectLimit_primeCast_eq_zero p hp A hA
  let F := projectivePrimePowerRingHom (A := FrobeniusDirectLimit A p hp hA) p hp hL
  have hinj : Function.Injective F := by
    apply (injective_iff_map_eq_zero F).mpr
    intro z hz
    obtain ⟨n, x, rfl⟩ := DirectLimit.exists_eq_mk (frobeniusDirectSystemMap A p hp hA) z
    apply (frobeniusDirectLimitOf_eq_zero_iff_nilpotent A p hp hA n x).mpr
    have hx : frobeniusDirectLimitOf A p hp hA n (x ^ p) = 0 := by
      rw [map_pow]
      exact hz
    obtain ⟨k, hk⟩ :=
      (frobeniusDirectLimitOf_eq_zero_iff_nilpotent A p hp hA n (x ^ p)).mp hx
    exact ⟨p * k, by rw [pow_mul, hk]⟩
  refine ⟨⟨hinj, ?_⟩⟩
  intro z
  obtain ⟨n, x, rfl⟩ := DirectLimit.exists_eq_mk (frobeniusDirectSystemMap A p hp hA) z
  refine ⟨frobeniusDirectLimitOf A p hp hA (n + 1) x, ?_⟩
  change (frobeniusDirectLimitOf A p hp hA (n + 1) x) ^ p =
    frobeniusDirectLimitOf A p hp hA n x
  rw [← map_pow]
  have h := DirectLimit.Ring.of_f (G := fun _ : ℕ ↦ A)
    (f := frobeniusDirectSystemMap A p hp hA) (Nat.le_succ n) x
  change frobeniusDirectLimitOf A p hp hA (n + 1)
    (frobeniusDirectSystemMap A p hp hA n (n + 1) (Nat.le_succ n) x) =
      frobeniusDirectLimitOf A p hp hA n x at h
  simpa only [frobeniusDirectSystemMap_apply, Nat.add_sub_cancel_left, pow_one] using h

/-- 計画M03：同じFrobenius順極限・構造射を保つ完全環の入口。 -/
def frobeniusDirectLimitDesc (p : ℕ) [Fact p.Prime]
    {C D : Type u} [CommRing C] [CommRing D] [PerfectRing D p]
    (hC : (p : C) = 0) (hD : (p : D) = 0) (f : C →+* D) :
    FrobeniusDirectLimit C p (Fact.out : p.Prime) hC →+* D := by
  exact (perfectFrobeniusLimitEquiv D p (Fact.out : p.Prime) hD
    (perfectRing_primePower_bijective D p (Fact.out : p.Prime) hD)).toRingHom.comp
    (frobeniusDirectLimitMap p (Fact.out : p.Prime) hC hD f)

/-- 計画M04：同じFrobenius順極限・構造射を保つ完全環の入口。 -/
theorem frobeniusDirectLimitDesc_comp_of_zero (p : ℕ) [Fact p.Prime]
    {C D : Type u} [CommRing C] [CommRing D] [PerfectRing D p]
    (hC : (p : C) = 0) (hD : (p : D) = 0) (f : C →+* D) :
    (frobeniusDirectLimitDesc p hC hD f).comp
      (frobeniusDirectLimitOf C p (Fact.out : p.Prime) hC 0) = f := by
  apply RingHom.ext
  intro x
  change perfectFrobeniusLimitEquiv D p (Fact.out : p.Prime) hD
    (perfectRing_primePower_bijective D p (Fact.out : p.Prime) hD)
    (frobeniusDirectLimitMap p (Fact.out : p.Prime) hC hD f
      (frobeniusDirectLimitOf C p (Fact.out : p.Prime) hC 0 x)) = f x
  rw [frobeniusDirectLimitMap_of]
  exact RingHom.congr_fun (perfectFrobeniusLimitEquiv_comp_of_zero D p (Fact.out : p.Prime)
    hD (perfectRing_primePower_bijective D p (Fact.out : p.Prime) hD)) (f x)

/-- 計画I00：同じFrobenius順極限・構造射を保つ完全環の入口。 -/
def perfectedAlgebraUnit (p : ℕ) [Fact p.Prime]
    (V C : Type u) [CommRing V] [CommRing C] [Algebra V C]
    (hp : (p : V) = 0) :
    V →+* FrobeniusDirectLimit C p (Fact.out : p.Prime)
      (by rw [← map_natCast (algebraMap V C), hp, map_zero]) := by
  exact (frobeniusDirectLimitOf C p (Fact.out : p.Prime)
    (by rw [← map_natCast (algebraMap V C), hp, map_zero]) 0).comp (algebraMap V C)

/-- 計画P00：同じFrobenius順極限・構造射を保つ完全環の入口。 -/
theorem perfectRing_pi_of_primeCast_eq_zero (p : ℕ) [Fact p.Prime]
    {ι : Type u} (V : ι → Type u) [∀ i, CommRing (V i)] [∀ i, PerfectRing (V i) p]
    (hp : ∀ i, (p : V i) = 0) : PerfectRing (∀ i, V i) p := by
  exact ⟨finitePi_primePower_bijective V p (Fact.out : p.Prime) hp
    (fun i ↦ perfectRing_primePower_bijective (V i) p (Fact.out : p.Prime) (hp i))⟩

end SerrePositivity.AlgebraicGeometry.ArcRouteB
