module

public import SerrePositivity.AlgebraicGeometry.ArcRouteB.CoverLaws
public import SerrePositivity.AlgebraicGeometry.ArcRouteB.FrobeniusPerfect
public import SerrePositivity.AlgebraicGeometry.ArcRouteB.UniversalCech
public import SerrePositivity.AlgebraicGeometry.ArcRouteB.FpResiduePoint
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.FiniteStability

/-!
概要：有限表示模型の剰余体上の点と、完全化した模型の底変換後の切断をつなぐ。
方針：rank0の付値試験でfiberの非零性を得て弱Nullstellensatzを使い、完全化への延長で切断を作る。
規約：指定された模型・係数と構造射を保つ。
使われ方：2iのI04・I07、BM18 Proposition 4.8(3),(4)。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory
open SerrePositivity
open scoped TensorProduct
namespace SerrePositivity.AlgebraicGeometry.ArcRouteB

/-- 計画I04：元の有限表示模型から剰余体の点と完全係数の切断への接続。 -/
theorem exists_fp_residue_point_of_perfectedArc
    (p : ℕ) [Fact p.Prime] {V C : Type u} [CommRing V] [IsDomain V]
    [ValuationRing V] [CommRing C] [Algebra V C] [Algebra.FinitePresentation V C]
    (hV : IsAbsolutelyIntegrallyClosed V) [PerfectRing V p] (hp : (p : V) = 0)
    (hf : IsArcHom (perfectedAlgebraUnit p V C hp)) (a : PrimeSpectrum V) :
    ∃ g : C →ₐ[V] a.asIdeal.ResidueField, True := by
  let K := a.asIdeal.ResidueField
  letI : IsAlgClosed K := hV.primeResidue_isAlgClosed a.asIdeal
  have hdim : ringKrullDim K ≤ 1 := by
    change Order.krullDim (PrimeSpectrum K) ≤ 1
    exact (Order.krullDim_nonpos_of_subsingleton : Order.krullDim (PrimeSpectrum K) ≤ 0).trans
      (by decide)
  obtain ⟨W, hW, hval, hdimW, e, l, he, hl⟩ :=
    hf (CommRingCat.of K) hdim (algebraMap V K)
  letI : IsDomain W := hW
  let hC : (p : C) = 0 := by rw [← map_natCast (algebraMap V C), hp, map_zero]
  let u := frobeniusDirectLimitOf C p (Fact.out : p.Prime) hC 0
  let φ : C →+* W := l.comp u
  have hc (v : V) : e (algebraMap V K v) = φ (algebraMap V C v) :=
    (RingHom.congr_fun hl v).symm
  let r := coefficientTensorLift e φ hc
  letI : Nontrivial (K ⊗[V] C) := r.domain_nontrivial
  obtain ⟨g⟩ := nonempty_algHom_of_isAlgClosed K (K ⊗[V] C)
  exact ⟨(g.restrictScalars V).comp Algebra.TensorProduct.includeRight, trivial⟩

/-- 計画I07：元の有限表示模型から剰余体の点と完全係数の切断への接続。 -/
theorem perfectedAlgebraUnit_universalExact_of_section
    (p : ℕ) [Fact p.Prime] {V C D : Type u} [CommRing V] [CommRing C]
    [CommRing D] [Algebra V C] [Algebra V D] [PerfectRing D p]
    (hp : (p : V) = 0) (g : C →ₐ[V] D) :
    PerfectRingCechUniversalExact p
      (arcBaseChangeHom (perfectedAlgebraUnit p V C hp) (algebraMap V D)) := by
  let gD : V →+* D := algebraMap V D
  let g0 : C →+* D := g.toRingHom
  have hg (v : V) : g0 (algebraMap V C v) = gD v := g.commutes v
  letI : Algebra V D := gD.toAlgebra
  let hC : (p : C) = 0 := by rw [← map_natCast (algebraMap V C), hp, map_zero]
  let hD : (p : D) = 0 := by rw [← map_natCast (algebraMap V D), hp, map_zero]
  let r := frobeniusDirectLimitDesc p hC hD g0
  letI := (perfectedAlgebraUnit p V C hp).toAlgebra
  have hc (v : V) : (RingHom.id D) (algebraMap V D v) =
      r (algebraMap V (FrobeniusDirectLimit C p (Fact.out : p.Prime) hC) v) := by
    change algebraMap V D v = r (frobeniusDirectLimitOf C p (Fact.out : p.Prime) hC 0
      (algebraMap V C v))
    have h := RingHom.congr_fun (frobeniusDirectLimitDesc_comp_of_zero p hC hD g0)
      (algebraMap V C v)
    exact (hg v).symm.trans h.symm
  let l := coefficientTensorLift (RingHom.id D) r hc
  let f0 := arcBaseChangeHom (perfectedAlgebraUnit p V C hp) gD
  have hsplit : l.comp f0 = RingHom.id D := by
    apply RingHom.ext
    intro d
    change l (d ⊗ₜ[V] (1 : FrobeniusDirectLimit C p (Fact.out : p.Prime) hC)) = d
    rw [coefficientTensorLift_tmul, map_one, mul_one]
    rfl
  exact perfectRingCechUniversalExact_of_flat_factor p f0 (RingHom.id D) l
    (RingHom.FaithfullyFlat.of_bijective Function.bijective_id) hsplit

end SerrePositivity.AlgebraicGeometry.ArcRouteB
