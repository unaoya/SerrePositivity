module

public import SerrePositivity.AlgebraicGeometry.ConnectedEtaleDomain
public import SerrePositivity.AlgebraicGeometry.NoetherianFiberComponent
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.LocalProperties.Basic

/-!
概要：体上の滑らかなアフィンの連結成分は整である。
方針：各点の標準 étale チャートから整域の主開を取り、既約性と被約性を合わせる。
規約：体の完全性は仮定しない。
使われ方：幾何学的連結な滑らかなファイバーを絶対既約な超曲面模型と比較する。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open Topology

private theorem irreducibleSpace_of_connected_of_open_irreducible
    {X : Type*} [TopologicalSpace X] [ConnectedSpace X]
    (h : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ IsIrreducible U) :
    IrreducibleSpace X := by
  let x : X := Classical.choice (inferInstance : Nonempty X)
  have hx : x ∈ ⋃₀ irreducibleComponents X := by
    rw [sUnion_irreducibleComponents]
    exact Set.mem_univ x
  obtain ⟨Z, hZ, _⟩ := hx
  have hOpen : IsOpen Z := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    obtain ⟨U, hU, hzU, hirr⟩ := h z
    let : IrreducibleSpace U := isIrreducible_iff_irreducibleSpace.mp hirr
    have hEmb : IsOpenEmbedding (Subtype.val : U → X) :=
      hU.isOpenEmbedding_subtypeVal
    have hNonempty : (Z ∩ Set.range (Subtype.val : U → X)).Nonempty :=
      ⟨z, hz, ⟨⟨z, hzU⟩, rfl⟩⟩
    have hPre := preimage_mem_irreducibleComponents hZ hEmb hNonempty
    rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hPre
    refine Filter.mem_of_superset (hU.mem_nhds hzU) ?_
    intro w hw
    change (⟨w, hw⟩ : U) ∈ (Subtype.val : U → X) ⁻¹' Z
    rw [hPre]
    exact Set.mem_univ _
  rcases isClopen_iff.mp ⟨isClosed_of_mem_irreducibleComponents Z hZ, hOpen⟩ with hEmpty | hAll
  · exact (hZ.1.nonempty.ne_empty hEmpty).elim
  · exact
      { isPreirreducible_univ := by rw [← hAll]; exact hZ.1.isPreirreducible
        toNonempty := inferInstance }

/--
概要：体上の滑らかな代数の各素点は、整域の主開近傍を持つ。
方針：標準 étale チャートの指定点を含む連結成分を取り、局所化を一段にまとめる。
規約：主開近傍は元の代数の一つの元の局所化として表す。
使われ方：滑らかな連結ファイバーの整性。
-/
theorem exists_isDomain_away_of_smooth_over_field
    {k B : Type*} [Field k] [CommRing B] [Algebra k B] [Algebra.Smooth k B]
    (p : PrimeSpectrum B) : ∃ b ∉ p.asIdeal, IsDomain (Localization.Away b) := by
  obtain ⟨b, hb, n, alg, tower, het⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := k) (p := p.asIdeal)
  let C := Localization.Away b
  let R := MvPolynomial (Fin n) k
  let : Algebra R C := alg
  let : IsScalarTower k R C := tower
  let : Algebra.IsStandardEtale R C := het
  let : IsIntegrallyClosed R := UniqueFactorizationMonoid.instIsIntegrallyClosed
  let : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing k C
  have hp : p ∈ Set.range (PrimeSpectrum.comap (algebraMap B C)) := by
    rw [PrimeSpectrum.localization_away_comap_range C b]
    exact hb
  obtain ⟨q, hq⟩ := hp
  obtain ⟨e, _, he⟩ := PrimeSpectrum.isClopen_iff.mp
    (isClopen_connectedComponent_of_noetherianSpace q)
  have heq : e ∉ q.asIdeal := by
    change q ∈ (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum C))
    rw [← he]
    exact mem_connectedComponent
  let D := Localization.Away e
  have hRange : Set.range (PrimeSpectrum.comap (algebraMap C D)) = connectedComponent q :=
    (PrimeSpectrum.localization_away_comap_range D e).trans he.symm
  let : ConnectedSpace (PrimeSpectrum D) := by
    let h := (PrimeSpectrum.localization_away_isOpenEmbedding D e).isEmbedding.toHomeomorph
    rw [h.connectedSpace_iff, ← isConnected_iff_connectedSpace, hRange]
    exact isConnected_connectedComponent
  let : IsDomain D := isDomain_of_connected_etale_over_normal_domain (A := R)
  obtain ⟨c, s, hs⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers b) e
  have hec : e * algebraMap B C s = algebraMap B C c :=
    hs ▸ IsLocalization.mk'_spec C c s
  have hu : IsUnit (algebraMap B C s) := IsLocalization.map_units C s
  have hAssoc : Associated e (algebraMap B C c) := ⟨hu.unit, by rw [hu.unit_spec, hec]⟩
  let : IsLocalization.Away (algebraMap B C c) D := IsLocalization.Away.of_associated hAssoc
  let : IsScalarTower B C D := OreLocalization.instIsScalarTower
  let : IsLocalization.Away (b * c) D := IsLocalization.Away.mul' C D b c
  have hcp : c ∉ p.asIdeal := by
    rw [← hq]
    change algebraMap B C c ∉ q.asIdeal
    rw [← hec]
    exact q.isPrime.mul_notMem heq (q.asIdeal.notMem_of_isUnit hu)
  let iso := IsLocalization.algEquiv (Submonoid.powers (b * c)) (Localization.Away (b * c)) D
  exact ⟨b * c, p.isPrime.mul_notMem hb hcp,
    Function.Injective.isDomain iso.toRingHom iso.injective⟩

/--
概要：体上の滑らかな代数のスペクトルが連結なら、その代数は整域。
方針：整域の主開近傍から既約性を得て、各極大点の局所化で冪零元の消滅を確かめる。
規約：連結性は空でないことを含む。
使われ方：滑らかな族の幾何学的連結な生成ファイバーを整な模型に移す。
-/
theorem isDomain_of_connected_smooth_over_field
    {k B : Type*} [Field k] [CommRing B] [Algebra k B] [Algebra.Smooth k B]
    [ConnectedSpace (PrimeSpectrum B)] : IsDomain B := by
  let : IrreducibleSpace (PrimeSpectrum B) :=
    irreducibleSpace_of_connected_of_open_irreducible fun p => by
      obtain ⟨b, hb, hD⟩ := exists_isDomain_away_of_smooth_over_field (k := k) p
      refine ⟨PrimeSpectrum.basicOpen b, (PrimeSpectrum.basicOpen b).isOpen, hb, ?_⟩
      rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away b) b, ← Set.image_univ]
      exact (IrreducibleSpace.isIrreducible_univ _).image _
        (PrimeSpectrum.continuous_comap _).continuousOn
  let : IsReduced B := ⟨fun z hz => by
    apply eq_zero_of_localization z
    intro p hp
    obtain ⟨b, hb, hD⟩ :=
      exists_isDomain_away_of_smooth_over_field (k := k) (⟨p, inferInstance⟩ : PrimeSpectrum B)
    let D := Localization.Away b
    have hu : IsUnit (algebraMap B (Localization.AtPrime p) b) :=
      IsLocalization.map_units _ (⟨b, hb⟩ : p.primeCompl)
    let g : D →+* Localization.AtPrime p := IsLocalization.Away.lift b hu
    have hzero : algebraMap B D z = 0 := (hz.map (algebraMap B D)).eq_zero
    rw [← IsLocalization.Away.lift_eq (S := D) b hu z]
    exact (congrArg g hzero).trans (map_zero g)⟩
  have hPrime := PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical (R := B) |>.mp inferInstance
  rw [nilradical_eq_zero, Ideal.zero_eq_bot] at hPrime
  exact (RingEquiv.quotientBot B).symm.isDomain

end SerrePositivity.AlgebraicGeometry
