module

public import SerrePositivity.CLMST.Prop247RankProduct
public import SerrePositivity.CommutativeAlgebra.FiniteSpectrumPartition
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.Localization.Pi

/-! # Prop 2.4.7：元の rank 像の有限直積は g の外で同型

各商の元の局所化写像を固定し、スペクトルの有限分割から既存 CRT で全単射性を得る。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (g : R) (hetale : letI := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g)))

/-- 原典の像への写像 R→Ri を g で局所化した元の環写像。 -/
abbrev prop247_awayToRankImage (n : ℕ) :=
  Localization.awayMap
    (prop247_toOpenSectionImage R (prop247_rankOpen R S g hetale n)).toRingHom g

theorem prop247_awayToRankImage_surjective (n : ℕ) :
    Function.Surjective (prop247_awayToRankImage R S g hetale n) :=
  IsLocalization.Away.mapₐ_surjective_of_surjective g
    (prop247_toOpenSectionImage_surjective R _)

/-- 各元の局所化写像の Spec の像は、元の局所化上の所定の rank ファイバーである。 -/
theorem prop247_awayToRankImage_spectrum_range [IsReduced R] (n : ℕ) :
    Set.range (PrimeSpectrum.comap (prop247_awayToRankImage R S g hetale n)) =
      {x | prop247_awayRank R S g (prop247_awaySpectrumHomeomorph R g x) = n} := by
  let U := prop247_rankOpen R S g hetale n
  let q := (prop247_toOpenSectionImage R U).toRingHom
  have hker : RingHom.ker (prop247_awayToRankImage R S g hetale n) =
      (PrimeSpectrum.vanishingIdeal (U : Set (PrimeSpectrum R))).map
        (algebraMap R (Localization.Away g)) := by
    have hk := IsLocalization.ker_map (S := Localization.Away g) (Localization.Away (q g)) q
      (Submonoid.map_powers q g)
    rw [show RingHom.ker q = PrimeSpectrum.vanishingIdeal (U : Set (PrimeSpectrum R)) from
      prop247_toOpenSectionImage_ker R U] at hk
    exact hk
  ext x
  rw [range_comap_of_surjective _ _ (prop247_awayToRankImage_surjective R S g hetale n), hker]
  change ((PrimeSpectrum.vanishingIdeal (U : Set (PrimeSpectrum R))).map
    (algebraMap R (Localization.Away g))) ≤ x.asIdeal ↔ _
  rw [Ideal.map_le_iff_le_comap]
  change PrimeSpectrum.comap (algebraMap R (Localization.Away g)) x ∈
    PrimeSpectrum.zeroLocus (PrimeSpectrum.vanishingIdeal (U : Set (PrimeSpectrum R)) : Set R) ↔ _
  rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
  have h := congrArg (fun Z => prop247_awaySpectrumHomeomorph R g x ∈ Z)
    (prop247_rankOpen_closure_on_away R S g hetale n)
  simpa only [Set.mem_preimage, prop247_awaySpectrumHomeomorph_apply, Set.mem_ofPred_eq]
    using Iff.of_eq h

/-- 元の有限直積写像を各成分で g に局所化すると全単射になる。
大域的な直積写像そのものの単射性・全射性は要求しない。 -/
theorem prop247_awayRankImageProduct_bijective [IsReduced R] (t : Finset ℕ)
    (ht : ∀ x : PrimeSpectrum.basicOpen g, prop247_awayRank R S g x ∈ t) :
    Function.Bijective (RingHom.pi (fun n : t => prop247_awayToRankImage R S g hetale n)) := by
  apply pi_ringHom_bijective_of_spectrum_partition (Localization.Away g)
    (fun n : t => Localization.Away
      ((prop247_toOpenSectionImage R (prop247_rankOpen R S g hetale n)) g))
    (fun n : t => prop247_awayToRankImage R S g hetale n)
    (fun n => prop247_awayToRankImage_surjective R S g hetale n)
  · intro i j hij
    rw [prop247_awayToRankImage_spectrum_range, prop247_awayToRankImage_spectrum_range]
    apply Set.disjoint_left.mpr
    intro x hi hj
    exact hij (Subtype.ext (hi.symm.trans hj))
  · ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    refine ⟨⟨prop247_awayRank R S g (prop247_awaySpectrumHomeomorph R g x),
      ht (prop247_awaySpectrumHomeomorph R g x)⟩, ?_⟩
    rw [prop247_awayToRankImage_spectrum_range]
    rfl

/-- 各成分の局所化の積との標準比較を介して、元の R→∏Ri 自体の局所化が全単射となる。 -/
theorem prop247_toRankImageProduct_away_bijective [IsReduced R] (t : Finset ℕ)
    (ht : ∀ x : PrimeSpectrum.basicOpen g, prop247_awayRank R S g x ∈ t) :
    Function.Bijective (Localization.awayMap
      (prop247_toRankImageProduct R S g hetale t).toRingHom g) := by
  let A := fun n : t => prop247_openSectionImage R (prop247_rankOpen R S g hetale n)
  let q := (prop247_toRankImageProduct R S g hetale t).toRingHom
  let B := fun n : t => Localization.Away
    ((prop247_toOpenSectionImage R (prop247_rankOpen R S g hetale n)) g)
  let M := Submonoid.powers (q g)
  letI (n : t) : IsLocalization (M.map (Pi.evalRingHom A n)) (B n) := by
    dsimp only [M]
    rw [Submonoid.map_powers]
    change IsLocalization
      (.powers ((prop247_toOpenSectionImage R (prop247_rankOpen R S g hetale n)) g))
      (Localization.Away ((prop247_toOpenSectionImage R (prop247_rankOpen R S g hetale n)) g))
    infer_instance
  letI : IsLocalization M ((n : t) → B n) :=
    (IsLocalization.iff_map_piEvalRingHom A ((n : t) → B n) M).mpr inferInstance
  let j := IsLocalization.algEquiv M (Localization.Away (q g)) ((n : t) → B n)
  have hs : j.toRingHom.comp (Localization.awayMap q g) =
      RingHom.pi (fun n : t => prop247_awayToRankImage R S g hetale n) := by
    apply IsLocalization.ringHom_ext (.powers g)
    ext r n
    change j (Localization.awayMap q g (algebraMap R (Localization.Away g) r)) n = _
    rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq, j.commutes]
    change algebraMap (A n) (B n) (q r n) =
      prop247_awayToRankImage R S g hetale n (algebraMap R (Localization.Away g) r)
    rw [prop247_awayToRankImage, Localization.awayMap, IsLocalization.Away.map,
      IsLocalization.map_eq]
    rfl
  have hb := prop247_awayRankImageProduct_bijective R S g hetale t ht
  constructor
  · intro x y h
    apply hb.1
    rw [← hs]
    exact congrArg j h
  · intro y
    obtain ⟨x, hx⟩ := hb.2 (j y)
    refine ⟨x, j.injective ?_⟩
    change (j.toRingHom.comp (Localization.awayMap q g)) x = j y
    rwa [hs]

end SerrePositivity.CLMST
