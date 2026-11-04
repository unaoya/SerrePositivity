module

public import SerrePositivity.CommutativeAlgebra.EtaleStratification.StratumLocalization

/-!
# 被約主開層の普遍性

## 概要
被約環への射が I を消し g を可逆にすれば、対応する層からの射に一意に延びる。

## 方針
I の根基も被約な終域では消えるので、商写像と局所化の普遍性を順に適用する。

## 規約
条件は I 自体に課す。根基を消すことは被約性から導く。

## 使われ方
底変換後の被約層と、被約テンソル積の比較。
-/

@[expose] public section
noncomputable section
universe u

namespace SerrePositivity.CommutativeAlgebra

/-- 被約環への射を被約主開層からの射へ延ばす。 -/
def stratumLift {R A : Type u} [CommRing R] [CommRing A] [IsReduced A]
    (I : Ideal R) (g : R) (f : R →+* A) (hI : I ≤ RingHom.ker f) (hg : IsUnit (f g)) :
    StratumRing I g →+* A := by
  let q : R ⧸ I.radical →+* A := Ideal.Quotient.lift I.radical f (by
    intro x hx
    obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hx
    exact (show IsNilpotent (f x) from ⟨n, by rw [← map_pow]; exact hI hn⟩).eq_zero)
  exact IsLocalization.Away.lift (Ideal.Quotient.mk I.radical g) (g := q) hg

@[simp]
theorem stratumLift_unit {R A : Type u} [CommRing R] [CommRing A] [IsReduced A]
    (I : Ideal R) (g : R) (f : R →+* A) (hI : I ≤ RingHom.ker f) (hg : IsUnit (f g)) (x : R) :
    stratumLift I g f hI hg (stratumUnit I g x) = f x := by
  simp only [stratumLift, stratumUnit, RingHom.comp_apply, IsLocalization.Away.lift_eq,
    Ideal.Quotient.lift_mk]

/-- 層の標準射は I 自体を消す。 -/
theorem stratumUnit_ker {R : Type u} [CommRing R] (I : Ideal R) (g : R) :
    I ≤ RingHom.ker (stratumUnit I g) :=
  fun x hx ↦ stratumUnit_eq_zero I g x (Ideal.le_radical hx)

/-- 根基による商でさらに局所化した環への延長は一意。 -/
theorem stratumLift_unique {R A : Type u} [CommRing R] [CommRing A] [IsReduced A]
    (I : Ideal R) (g : R) (f : R →+* A) (hI : I ≤ RingHom.ker f) (hg : IsUnit (f g))
    (k : StratumRing I g →+* A) (hk : k.comp (stratumUnit I g) = f) :
    k = stratumLift I g f hI hg := by
  apply stratumRing_hom_ext I g
  intro x
  rw [stratumLift_unit]
  exact RingHom.congr_fun hk x

end SerrePositivity.CommutativeAlgebra
