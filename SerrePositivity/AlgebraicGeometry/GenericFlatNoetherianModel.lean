module

public import SerrePositivity.AlgebraicGeometry.GenericFreeNoetherianModel
public import SerrePositivity.AlgebraicGeometry.GenericFlatNoetherianOpen
public import SerrePositivity.AlgebraicGeometry.ValuativeOpenImageGenerizations
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
概要：有限表示アフィン射の Noether 模型に、元の基底の全一般点を含む平坦開を添える。
方針：模型上の一般自由基本開を和にし、その逆像の準コンパクト性と稠密性を示す。
規約：模型への実際の tensor 同型を保持する。
使われ方：Rydh 3.7 の Noether 平坦化に渡す指定開。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
open scoped TensorProduct
universe u

set_option backward.isDefEq.respectTransparency false in
/-- 有限表示代数の Noether 模型には、元の全一般点を覆う準コンパクトな平坦開を添えられる。 -/
theorem exists_generic_flat_noetherian_model
    (R B : Type u) [CommRing R] [IsReduced R] [CommRing B] [Algebra R B]
    [Algebra.FinitePresentation R B]
    (hmin : IsCompact {q : PrimeSpectrum R | q.asIdeal ∈ minimalPrimes R}) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra ℤ A) (_ : Algebra A R)
      (S : Type u) (_ : CommRing S) (_ : Algebra A S),
      Algebra.FiniteType ℤ A ∧ IsNoetherianRing A ∧ Algebra.FinitePresentation A S ∧
        Nonempty (R ⊗[A] S ≃ₐ[R] B) ∧ ∃ U : (Spec (CommRingCat.of A)).Opens,
          IsCompact U.carrier ∧
          Flat (Spec.map (CommRingCat.ofHom (algebraMap A S)) ∣_ U) ∧
          IsCompact (Spec.map (CommRingCat.ofHom (algebraMap A R)) ⁻¹ᵁ U).carrier ∧
          Dense (Spec.map (CommRingCat.ofHom (algebraMap A R)) ⁻¹ᵁ U).carrier ∧
          ∀ q : PrimeSpectrum R, q.asIdeal ∈ minimalPrimes R →
            q ∈ Spec.map (CommRingCat.ofHom (algebraMap A R)) ⁻¹ᵁ U := by
  obtain ⟨A, _, _, _, S, _, _, hA, hN, hS, he, n, t, hfree, hcov⟩ :=
    exists_generic_free_noetherian_model R B hmin
  letI : IsNoetherianRing A := hN
  let U : (Spec (CommRingCat.of A)).Opens := ⨆ i, PrimeSpectrum.basicOpen (t i)
  let g := Spec.map (CommRingCat.ofHom (algebraMap A R))
  have hUc : IsCompact U.carrier := TopologicalSpace.NoetherianSpace.isCompact _
  have hflat : Flat (Spec.map (CommRingCat.ofHom (algebraMap A S)) ∣_ U) :=
    flat_restrict_iSup_basicOpen_of_free_tensor (CommRingCat.of A) (CommRingCat.of S) t hfree
  have hMU (q : PrimeSpectrum R) (hq : q.asIdeal ∈ minimalPrimes R) : q ∈ g ⁻¹ᵁ U := by
    obtain ⟨i, hi⟩ := hcov q hq
    change g q ∈ U
    apply TopologicalSpace.Opens.mem_iSup.mpr
    refine ⟨i, ?_⟩
    change algebraMap A R (t i) ∉ q.asIdeal
    exact hi
  obtain ⟨V, _, hVd, hVU, _⟩ := exists_compact_denseOpen_of_contains_minimalPrimes
    (CommRingCat.of R) hmin (g ⁻¹ᵁ U) hMU
  refine ⟨A, inferInstance, inferInstance, inferInstance, S, inferInstance, inferInstance,
    hA, hN, hS, he, U, hUc, hflat, g.isCompact_preimage hUc, hVd.mono hVU, hMU⟩

end SerrePositivity.AlgebraicGeometry
