module

public import SerrePositivity.AlgebraicGeometry.EtaleFlatCenterDescent
public import SerrePositivity.AlgebraicGeometry.EtaleLocalFiberInduction
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
概要：有限型アフィン始域上の各点の局所中心を、台の次元帰納から得た一つの中心にまとめる。
方針：étale 局所模型の像は開なので有限部分被覆を選び、共通中心で平坦性を降下する。
規約：各ファイバーの次元は同じ自然数で抑える。
使われ方：Stacks 0815 の次元帰納の後続段階。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory
open scoped TensorProduct

private theorem exists_pow_mem_of_basicOpen_le_affineCenterComplement
    {B : Type*} [CommRing B] (a : B) (I : Ideal B)
    (h : PrimeSpectrum.basicOpen a ≤ affineCenterComplement I) : ∃ n : ℕ, a ^ n ∈ I := by
  apply Ideal.mem_radical_iff.mp
  rw [← PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical, PrimeSpectrum.mem_vanishingIdeal]
  intro x hx
  by_contra hxa
  exact (mem_affineCenterComplement I x).mp (h hxa) hx

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1500000 in
-- 有限部分被覆の上で局所の代数構造を一斉に組み立てる。
/--
概要：相対次元を抑えた étale 局所模型を有限個選ぶと、より小さい台の次元に関する帰納仮定から中心を作れる。
方針：各点で有限押し出しにより中心を作り、étale 写像の像の有限部分被覆で降下する。
規約：境界は正則な一元で表す。
使われ方：零化イデアルの商のファイバーの次元上限を帰納の後続段階に使う。
-/
theorem exists_affine_flatPure_center_of_fiber_dimension_induction
    (R B : CommRingCat.{u}) [IsNoetherianRing R] [Algebra R B] [Algebra.FiniteType R B]
    {M : Type u} [AddCommGroup M] [Module R M] [Module B M] [IsScalarTower R B M]
    [Module.Finite B M] (a : R) (ha : IsRegular a)
    [Module.Flat (Localization.Away a) (Localization.Away a ⊗[R] M)]
    (d : ℕ) (hd : ∀ p : PrimeSpectrum R, ringKrullDim (p.asIdeal.Fiber B) ≤ d)
    (hrec : HasAffineFlatPureCentersBelow.{u} d) :
    ∃ I : Ideal R, I.FG ∧ PrimeSpectrum.basicOpen a ≤ affineCenterComplement I ∧
      HasFlatPurePullbacks (affineBlowupπ I) a M := by
  classical
  choose C D e j g q' he hj hq hcomm hlocal using fun q =>
    exists_etale_local_flatPure_center_at R B (M := M) a ha d hd hrec q
  let U (q : PrimeSpectrum B) : Set (PrimeSpectrum B) :=
    Set.range (Spec.map (j q))
  have hopen (q : PrimeSpectrum B) : IsOpen (U q) := by
    let : Etale (Spec.map (j q)) := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (hj q)
    exact (Spec.map (j q)).isOpenMap.isOpen_range
  have hU : (Set.univ : Set (PrimeSpectrum B)) ⊆ ⋃ q, U q := by
    intro q _
    exact Set.mem_iUnion.mpr ⟨q, q' q, hq q⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hopen hU
  let E (i : s) := C i.1
  let F (i : s) := D i.1
  let : ∀ i, Algebra R (E i) := fun i => (e i.1).hom.toAlgebra
  let : ∀ i, Algebra R (F i) := fun i => (e i.1 ≫ g i.1).hom.toAlgebra
  let : ∀ i, Algebra (E i) (F i) := fun i => (g i.1).hom.toAlgebra
  let : ∀ i, Algebra B (F i) := fun i => (j i.1).hom.toAlgebra
  let : ∀ i, IsScalarTower R (E i) (F i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
  let : ∀ i, IsScalarTower R B (F i) := fun i =>
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom (hcomm i.1))
  let : ∀ i, Algebra.Etale R (E i) := fun i => he i.1
  let : ∀ i, Algebra.Etale B (F i) := fun i => hj i.1
  have hcover (q : PrimeSpectrum B) : ∃ (i : s) (t : PrimeSpectrum (F i)),
      t.comap (algebraMap B (F i)) = q := by
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp (hs (Set.mem_univ q))
    obtain ⟨hps, t, ht⟩ := Set.mem_iUnion.mp hp
    exact ⟨⟨p, hps⟩, t, ht⟩
  have hloc (i : s) := hlocal i.1
  choose J _ hJ hJflat using hloc
  apply exists_affine_flatPure_center_of_etale_source_centers
    (fun i : s => E i) (fun i : s => F i) hcover a ha J _ hJflat
  intro i
  obtain ⟨k, hk⟩ := exists_pow_mem_of_basicOpen_le_affineCenterComplement _ _ (hJ i)
  exact ⟨k, by rwa [map_pow]⟩

end SerrePositivity.AlgebraicGeometry
