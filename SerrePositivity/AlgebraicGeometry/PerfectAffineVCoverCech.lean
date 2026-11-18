module

public import SerrePositivity.AlgebraicGeometry.PerfectFrobeniusCechComparison
public import SerrePositivity.AlgebraicGeometry.AffineVCoverFamily
public import Mathlib.FieldTheory.Perfect

/-!
概要：完全F_p代数の有限族のv被覆について、元の増大Čech複体の完全性を得る。
方針：同じ積への一射の付値判定と、点ごとのp乗の全単射性を使う。
規約：元の有限族・環の射・増大項を保ち、draftsのG-A6-1aと同じ型へ戻す。
使われ方：BS17 Theorem 4.1(i)、n=1・E=O・affine・有限族の出口（H04）。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u

/-- 同じ有限族の元のČech完全性への接続（計画H04a）。 -/
theorem finitePi_primeCast_eq_zero {ι : Type u} (B : ι → Type u)
    [∀ i, CommRing (B i)] (p : ℕ) (hB : ∀ i, (p : B i) = 0) :
    (p : ∀ i, B i) = 0 := by
  funext i
  exact hB i

/-- 同じ有限族の元のČech完全性への接続（計画H04b）。 -/
theorem finitePi_primePower_bijective {ι : Type u} (B : ι → Type u)
    [∀ i, CommRing (B i)] (p : ℕ) (hp : p.Prime) (hB : ∀ i, (p : B i) = 0)
    (hFB : ∀ i, Function.Bijective
      (projectivePrimePowerRingHom (A := B i) p hp (hB i))) :
    Function.Bijective (projectivePrimePowerRingHom (A := ∀ i, B i) p hp
      (finitePi_primeCast_eq_zero B p hB)) := by
  classical
  constructor
  · intro x y h
    funext i
    apply (hFB i).1
    exact congrFun h i
  · intro x
    choose y hy using (fun i ↦ (hFB i).2 (x i))
    exact ⟨y, funext hy⟩

/-- 同じ有限族の元のČech完全性への接続（計画H04c）。 -/
theorem perfectRing_primePower_bijective
    (A : Type u) [CommRing A] (p : ℕ) (hp : p.Prime) [PerfectRing A p]
    (hA : (p : A) = 0) :
    Function.Bijective (projectivePrimePowerRingHom (A := A) p hp hA) := by
  exact PerfectRing.bijective_frobenius

/-- 同じ有限族の元のČech完全性への接続（計画H04d）。 -/
theorem cech_exact_of_vCover_perfect
    (p : ℕ) [Fact p.Prime]
    {A : Type u} [CommRing A] [CharP A p] [PerfectRing A p]
    {ι : Type u} [Finite ι] (B : ι → Type u) [∀ i, CommRing (B i)]
    [∀ i, CharP (B i) p] [∀ i, PerfectRing (B i) p]
    (f : ∀ i, A →+* B i) (hf : IsAffineVCoverFamily B f) :
    SerrePositivity.Cech.AugmentedRingCechExact
      (Arrow.mk (CommRingCat.ofHom (RingHom.pi f))).augmentedCechConerve := by
  let hp : p.Prime := Fact.out
  have hA : (p : A) = 0 := CharP.cast_eq_zero A p
  have hB : ∀ i, (p : B i) = 0 := fun i ↦ CharP.cast_eq_zero (B i) p
  exact perfectAffineVCover_cechExact (RingHom.pi f) p hp hA
    (finitePi_primeCast_eq_zero B p hB)
    (perfectRing_primePower_bijective A p hp hA)
    (finitePi_primePower_bijective B p hp hB
      (fun i ↦ perfectRing_primePower_bijective (B i) p hp (hB i)))
    ((isAffineVCoverFamily_iff_pi B f).mp hf)

end SerrePositivity.AlgebraicGeometry
