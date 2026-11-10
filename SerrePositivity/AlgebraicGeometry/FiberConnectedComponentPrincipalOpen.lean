module

public import SerrePositivity.AlgebraicGeometry.NoetherianFiberComponent
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-!
概要：指定点を通るファイバーの連結成分を、始域の主開で切り出す。
方針：成分を定める冪等元の分母を払い、ファイバーの局所化と始域の局所化を比較する。
規約：指定点は剰余体の拡大体に値を取る点とする。
使われ方：相対 Noether 正規化先で指定成分だけを広げる。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open TopologicalSpace
open scoped TensorProduct

/--
概要：指定ファイバーの体値点を残す主開で、その点を通るファイバーの連結成分を切り出せる。
方針：連結成分の冪等元を剰余体の分母で払って、元の代数の一つの元に置き換える。
規約：指定点の持ち上げは、元の代数の元に対して同じ値を取る。
使われ方：純超越な点を持つ指定成分に有限標識を構成する。
-/
theorem exists_away_connected_fiber_of_point
    {R B F : Type*} [CommRing R] [CommRing B] [Field F] [Algebra R B]
    [Algebra.FiniteType R B] (p : Ideal R) [p.IsPrime] [Algebra p.ResidueField F]
    (y : p.Fiber B →ₐ[p.ResidueField] F) :
    ∃ b : B, y (1 ⊗ₜ[R] b) ≠ 0 ∧
      ConnectedSpace (PrimeSpectrum (p.Fiber (Localization.Away b))) ∧
      Set.range (PrimeSpectrum.comap
        (Algebra.TensorProduct.map (AlgHom.id p.ResidueField p.ResidueField)
          (IsScalarTower.toAlgHom R B (Localization.Away b))).toRingHom) =
        connectedComponent ((⊥ : PrimeSpectrum F).comap y.toRingHom) ∧
      ∃ z : p.Fiber (Localization.Away b) →ₐ[p.ResidueField] F,
        ∀ t : B, z (1 ⊗ₜ[R] algebraMap B (Localization.Away b) t) = y (1 ⊗ₜ[R] t) := by
  let k := p.ResidueField
  let E := p.Fiber B
  let q := (⊥ : PrimeSpectrum F).comap y.toRingHom
  let : IsNoetherianRing E := Algebra.FiniteType.isNoetherianRing k E
  obtain ⟨e, _, hC⟩ := PrimeSpectrum.isClopen_iff.mp
    (isClopen_connectedComponent_of_noetherianSpace q)
  obtain ⟨a, ha, b, hb⟩ := Ideal.Fiber.exists_smul_eq_one_tmul p e
  let c : E := 1 ⊗ₜ[R] b
  have hu : IsUnit (algebraMap R E a) := by
    rw [IsScalarTower.algebraMap_apply R k E]
    exact (isUnit_iff_ne_zero.mpr
      (fun h => ha (Ideal.algebraMap_residueField_eq_zero.mp h))).map (algebraMap k E)
  have hc : (PrimeSpectrum.basicOpen c : Set (PrimeSpectrum E)) = PrimeSpectrum.basicOpen e := by
    have hec : c = a • e := hb.symm
    ext t
    change (c ∉ t.asIdeal) ↔ (e ∉ t.asIdeal)
    rw [hec, Algebra.smul_def]
    rw [Ideal.IsPrime.mul_mem_left_iff (t.asIdeal.notMem_of_isUnit hu)]
  have hyc : y c ≠ 0 := by
    have hq : q ∈ (PrimeSpectrum.basicOpen c : Set (PrimeSpectrum E)) := by
      rw [hc, ← hC]
      exact mem_connectedComponent
    exact (PrimeSpectrum.mem_basicOpen c q).mp hq
  let C := Localization.Away c
  have hRange : Set.range (PrimeSpectrum.comap (algebraMap E C)) = connectedComponent q :=
    (PrimeSpectrum.localization_away_comap_range C c).trans (hc.trans hC.symm)
  let : ConnectedSpace (PrimeSpectrum C) := by
    let h := (PrimeSpectrum.localization_away_isOpenEmbedding C c).isEmbedding.toHomeomorph
    rw [h.connectedSpace_iff, ← isConnected_iff_connectedSpace, hRange]
    exact isConnected_connectedComponent
  let L := Localization.Away b
  let h := IsLocalization.Away.tensorProductEquivTMulRight R k b L
  let j : E →ₐ[k] (k ⊗[R] L) :=
    Algebra.TensorProduct.map (AlgHom.id k k) (IsScalarTower.toAlgHom R B L)
  have hj : h.toAlgHom.comp j = IsScalarTower.toAlgHom k E C := by
    apply Algebra.TensorProduct.ext'
    intro r t
    change h (r ⊗ₜ[R] algebraMap B L t) = algebraMap E C (r ⊗ₜ[R] t)
    exact IsLocalization.Away.tensorProductEquivTMulRight_tmul (R := R) (A := B) b L r t
  let H := PrimeSpectrum.homeomorphOfRingEquiv h.toRingEquiv
  have hFull : Set.range (PrimeSpectrum.comap j.toRingHom) = connectedComponent q := by
    have hSurj : Function.Surjective (PrimeSpectrum.comap h.toRingHom) := H.symm.surjective
    calc
      Set.range (PrimeSpectrum.comap j.toRingHom) =
          Set.range (PrimeSpectrum.comap j.toRingHom ∘ PrimeSpectrum.comap h.toRingHom) := by
        rw [Set.range_comp, hSurj.range_eq, Set.image_univ]
      _ = Set.range (PrimeSpectrum.comap (algebraMap E C)) := by
        rw [← PrimeSpectrum.comap_comp]
        exact congrArg (fun f => Set.range (PrimeSpectrum.comap f.toRingHom)) hj
      _ = connectedComponent q := hRange
  let z : C →ₐ[k] F := IsLocalization.Away.liftAlgHom c (f := y) (isUnit_iff_ne_zero.mpr hyc)
  refine ⟨b, hyc, H.connectedSpace_iff.mpr inferInstance, hFull, z.comp h.toAlgHom, ?_⟩
  intro t
  change z (h ((1 : k) ⊗ₜ[R] algebraMap B L t)) = _
  rw [show h ((1 : k) ⊗ₜ[R] algebraMap B L t) = algebraMap E C ((1 : k) ⊗ₜ[R] t) from
    IsLocalization.Away.tensorProductEquivTMulRight_tmul (R := R) (A := B) b L 1 t]
  exact IsLocalization.Away.lift_eq c (isUnit_iff_ne_zero.mpr hyc) _

end SerrePositivity.AlgebraicGeometry
