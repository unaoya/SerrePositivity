module

public import SerrePositivity.BhattScholze.Perfectoidization.RootTower
public import SerrePositivity.LengthAlgebra.RootTowerLength.Tower
public import SerrePositivity.CLMST.CyclicLengthBound
public import SerrePositivity.CLMST.KoszulAnnihilation
public import SerrePositivity.CLMST.ParameterPowerLength

/-! # 混標数の長さ代数（CLMST の引用）

## 概要

`C_D = (R∞ ⊗_A D)_perfd` に CLMST の三つの結果を適用し、高次 Koszul ホモロジーの正規化長さの消滅と、零次のパラメータ商の長さを得て、完備化前の塔の `towerLengthOn` と同定する。

## 方針

Corollary 4.0.4 の almost 消滅（`CLMST.exists_perfectoidIdeal_annihilates_koszul`）に独立に示した一様な冪ねじれを組み合わせて Proposition 4.0.10（`CLMST.completedLength_eq_zero_of_perfectoidIdeal_annihilates`）を使い、零次には Proposition 4.0.14（`CLMST.parameter_quotient_length`）を使う。

## 規約

直接の `sorry` はない。三つの結果は CLMST/KoszulAnnihilation・CyclicLengthBound・ParameterPowerLength にあり、文献の未証明入力（BS Thm 1.17(1)・Cor 8.12 など）は BhattScholze の Inputs に明示されている。出典：Cai–Lee–Ma–Schwede–Tucker, arXiv:2209.04046v4。

## 使われ方

`Paper/Section2/LengthAlgebra`。
-/

public section

universe u

section MixedLengthAlgebraPart

open IsLocalRing
open scoped ENNReal
namespace SerrePositivity.Section2

/-- 混標数の具体的な perfectoid 化は、定理2.5の二つの長さの性質を満たす。
almost 消滅、冪ねじれ、長さ零への変換を別々に適用し、最後に係数を制限する。 -/
theorem mixedPerfectoid_length_properties
    (A D : Type u) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    [CommRing D] [IsLocalRing D] [IsNoetherianRing D] [IsDomain D]
    [IsAdicComplete (maximalIdeal D) D] [Algebra A D] [Module.Finite A D]
    (hinj : Function.Injective (algebraMap A D))
    (hres : Function.Surjective ((residue D).comp (algebraMap A D)))
    {h : ℕ} (t : Fin h → A) (hdimA : ringKrullDim A = h) (hdimD : ringKrullDim D = h)
    (hpos : 0 < h) (ht : Ideal.span (Set.range t) = maximalIdeal A)
    (hsop : IsSystemOfParameters D (algebraMap A D ∘ t))
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField D) p] [PerfectField (ResidueField D)]
    [CharZero D] (htp : t ⟨0, hpos⟩ = (p : A))
    (e : A ≃+* MvPowerSeries {i : Fin h // (i : ℕ) ≠ 0} (WittVector p (ResidueField D)))
    (he : ∀ (i : Fin h) (hi : (i : ℕ) ≠ 0), e (t i) = MvPowerSeries.X ⟨i, hi⟩)
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p) :
    (∀ (z : Fin h → D), IsSystemOfParameters D z → ∀ i : ℕ, 0 < i →
      (towerLengthOn A D hinj t p
        (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i)) (MixedPerfectoid A D t p hperf)).len
        (koszulHomologySelf (fun j ↦ algebraMap D (MixedPerfectoid A D t p hperf) (z j)) i) = 0) ∧
    (∀ (z : Fin h → D), IsSystemOfParameters D z →
      (towerLengthOn A D hinj t p
        (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i)) (MixedPerfectoid A D t p hperf)).len
        ((MixedPerfectoid A D t p hperf) ⧸
          Ideal.span (Set.range fun j ↦ algebraMap D (MixedPerfectoid A D t p hperf) (z j))) =
        ENNReal.ofReal (HilbertSamuel.multiplicity D (Ideal.span (Set.range z)) D : ℝ)) := by
  obtain ⟨g, hg, hann⟩ := CLMST.exists_perfectoidIdeal_annihilates_koszul
    A D hinj hres t hdimA hdimD hpos ht hsop p htp e he hperf
  constructor
  · intro z hz i hi
    rw [towerLengthOn_eq_completedTowerLength A t p
      (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i)) D hinj]
    let := Module.compHom
      (koszulHomologySelf (fun j ↦ algebraMap D (MixedPerfectoid A D t p hperf) (z j)) i)
      (algebraMap (CompletedTower A t p) (MixedPerfectoid A D t p hperf))
    exact CLMST.completedLength_eq_zero_of_perfectoidIdeal_annihilates
      A (ResidueField D) p t hpos htp ht hdimA e he hperf g hg _
      (isPowTorsion_completedTower_koszul A t p D hinj (MixedPerfectoid A D t p hperf) z hz i)
      (hann z hz i hi)
  · intro z hz
    rw [towerLengthOn_eq_completedTowerLength A t p
      (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i)) D hinj]
    exact CLMST.parameter_quotient_length
      A D hinj hres t hdimA hdimD hpos ht hsop p htp e he hperf z hz

end SerrePositivity.Section2

end MixedLengthAlgebraPart
