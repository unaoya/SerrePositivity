module

public import SerrePositivity.CLMST.Prop247RankImages

/-! # Prop 2.4.7：原典の像の環の有限直積への元の写像

rank 分解の有限集合に対し R→∏Ri を固定する。
perfectoid 化を行う前の有限性と核・Spec の像を計算する。
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
    (t : Finset ℕ)

/-- 原典の各切断への像の環の有限直積。空の直積も許す。 -/
abbrev prop247_rankImageProduct : Type u :=
  (n : t) → prop247_openSectionImage R (prop247_rankOpen R S g hetale n)

/-- 元の R の元を、各 rank 部分の元の切断の像へ送る写像。 -/
def prop247_toRankImageProduct : R →ₐ[R] prop247_rankImageProduct R S g hetale t :=
  AlgHom.pi (fun n => prop247_toOpenSectionImage R (prop247_rankOpen R S g hetale n))

/-- 有限直積への写像は有限な環写像である。Ri の有限表示性は要求しない。 -/
theorem prop247_rankImageProduct_finite :
    Module.Finite R (prop247_rankImageProduct R S g hetale t) := by
  letI (n : t) : Module.Finite R
      (prop247_openSectionImage R (prop247_rankOpen R S g hetale n)) :=
    prop247_openSectionImage_finite R _
  infer_instance

/-- 元の rank 分解の有限集合が与えられれば、その実開集合の和は D(g) である。 -/
theorem prop247_rankOpen_iUnion
    (ht : ∀ x : PrimeSpectrum.basicOpen g, prop247_awayRank R S g x ∈ t) :
    (⋃ n : t, (prop247_rankOpen R S g hetale n : Set (PrimeSpectrum R))) =
      (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum R)) := by
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨n, y, _hy, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨prop247_awayRank R S g ⟨x, hx⟩, ht ⟨x, hx⟩⟩, ⟨x, hx⟩, rfl, rfl⟩

/-- 被約基底では、有限直積の Spec の実像は D(g) の閉包である。 -/
theorem prop247_rankImageProduct_spectrum_range [IsReduced R]
    (ht : ∀ x : PrimeSpectrum.basicOpen g, prop247_awayRank R S g x ∈ t) :
    Set.range (PrimeSpectrum.comap (prop247_toRankImageProduct R S g hetale t).toRingHom) =
      closure (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum R)) := by
  rw [← PrimeSpectrum.iUnion_range_comap_comp_evalRingHom
    (prop247_toRankImageProduct R S g hetale t).toRingHom]
  change (⋃ n : t, Set.range (PrimeSpectrum.comap
    (prop247_toOpenSectionImage R (prop247_rankOpen R S g hetale n)).toRingHom)) = _
  simp_rw [prop247_openSectionImage_spectrum_range]
  rw [← closure_iUnion_of_finite, prop247_rankOpen_iUnion R S g hetale t ht]

/-- 有限直積への元の写像の核は D(g) の消滅イデアルである。 -/
theorem prop247_toRankImageProduct_ker [IsReduced R]
    (ht : ∀ x : PrimeSpectrum.basicOpen g, prop247_awayRank R S g x ∈ t) :
    RingHom.ker (prop247_toRankImageProduct R S g hetale t).toRingHom =
      PrimeSpectrum.vanishingIdeal (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum R)) := by
  ext a
  change (fun n : t => prop247_toOpenSectionImage R
    (prop247_rankOpen R S g hetale n) a) = 0 ↔ _
  have hn (n : t) : prop247_toOpenSectionImage R
      (prop247_rankOpen R S g hetale n) a = 0 ↔
      ∀ x ∈ (prop247_rankOpen R S g hetale n), a ∈ x.asIdeal := by
    change a ∈ RingHom.ker (prop247_toOpenSectionImage R
      (prop247_rankOpen R S g hetale n)).toRingHom ↔ _
    rw [prop247_toOpenSectionImage_ker, PrimeSpectrum.mem_vanishingIdeal]
    rfl
  rw [PrimeSpectrum.mem_vanishingIdeal]
  constructor
  · intro h x hx
    let n : t := ⟨prop247_awayRank R S g ⟨x, hx⟩, ht ⟨x, hx⟩⟩
    exact (hn n).mp (congrFun h n) x ⟨⟨x, hx⟩, rfl, rfl⟩
  · intro h
    funext n
    apply (hn n).mpr
    rintro x ⟨y, _hy, rfl⟩
    exact h y.1 y.2

end SerrePositivity.CLMST
