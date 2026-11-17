module

public import SerrePositivity.AlgebraicGeometry.PerfectFrobeniusDirectLimit
public import SerrePositivity.AlgebraicGeometry.FrobeniusAugmentedRingCoefficients
public import SerrePositivity.AlgebraicGeometry.AffineVCoverFrobeniusCechExact
public import SerrePositivity.HomologicalAlgebra.Cech.Basic

/-!
概要：完全な元の環の矢印と増大conerveへ、同じFrobenius係数から戻す。
方針：順極限の自然な同型をArrowと実際の増大conerveへ送り、完全性を移す。
規約：元の環の射・増大項・全次数を保持する。H02aは既存のχをそのまま用いる。
使われ方：BS17 Theorem 4.1(i)の指定されたaffine構造層のČech版（H02・H03）。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u

/-- 元の完全環と同じconerveのČech比較（計画H02b）。 -/
def perfectFrobeniusOriginalArrowIso {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0) (hB : (p : B) = 0)
    (hFA : Function.Bijective (projectivePrimePowerRingHom (A := A) p hp hA))
    (hFB : Function.Bijective (projectivePrimePowerRingHom (A := B) p hp hB)) :
    Arrow.mk (CommRingCat.ofHom (frobeniusDirectLimitMap p hp hA hB f)) ≅
      Arrow.mk (CommRingCat.ofHom f) := by
  refine Arrow.isoMk (perfectFrobeniusLimitEquiv A p hp hA hFA).toCommRingCatIso
    (perfectFrobeniusLimitEquiv B p hp hB hFB).toCommRingCatIso ?_
  apply CommRingCat.hom_ext
  exact (perfectFrobeniusLimitEquiv_naturality f p hp hA hB hFA hFB).symm

/-- 元の完全環と同じconerveのČech比較（計画H02c）。 -/
def perfectFrobeniusOriginalCechIso {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0) (hB : (p : B) = 0)
    (hFA : Function.Bijective (projectivePrimePowerRingHom (A := A) p hp hA))
    (hFB : Function.Bijective (projectivePrimePowerRingHom (A := B) p hp hB)) :
    frobeniusAugmentedRingCoefficients (Arrow.mk (CommRingCat.ofHom f)) p hp hA ≅
      (Arrow.mk (CommRingCat.ofHom f)).augmentedCechConerve :=
  frobeniusAugmentedRingCoefficientsIso (Arrow.mk (CommRingCat.ofHom f)) p hp hA hB ≪≫
    (CosimplicialObject.augmentedCechConerve (C := CommRingCat.{u})).mapIso
      (perfectFrobeniusOriginalArrowIso f p hp hA hB hFA hFB)

/-- 元の完全環と同じconerveのČech比較（計画H03a）。 -/
theorem perfectAffineVCover_cechExact {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0) (hB : (p : B) = 0)
    (hFA : Function.Bijective (projectivePrimePowerRingHom (A := A) p hp hA))
    (hFB : Function.Bijective (projectivePrimePowerRingHom (A := B) p hp hB))
    (hv : IsAffineVCover f) : SerrePositivity.Cech.AugmentedRingCechExact
      (Arrow.mk (CommRingCat.ofHom f)).augmentedCechConerve := by
  exact (SerrePositivity.Cech.ringCechExact_iff_of_iso
    (perfectFrobeniusOriginalCechIso f p hp hA hB hFA hFB)).mp
      (affineVCover_frobeniusCechExact f hv p hp hA)

end SerrePositivity.AlgebraicGeometry
