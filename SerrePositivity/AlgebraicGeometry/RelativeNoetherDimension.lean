module

public import SerrePositivity.AlgebraicGeometry.FiberDimensionBound
public import Mathlib.RingTheory.Etale.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Localization.BaseChange

/-!
概要：ファイバーの指定点で次元を制御し、アフィン空間上の étale 局所有限化を作る。
方針：主開上の Noether 正規化を準有限性に移し、準有限代数の局所有限化を適用する。
規約：相対次元の上限はアフィン空間の変数の数で表す。
使われ方：平坦化で、台のファイバー次元を増やさず有限な射に移る。
-/

@[expose] public noncomputable section

universe u v

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory Topology
open scoped TensorProduct

private theorem quasiFiniteAt_of_finite_fiberMap
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Algebra.FiniteType A B] (p : PrimeSpectrum R) (x : PrimeSpectrum B)
    (hx : x.comap (algebraMap R B) = p)
    (hfin : (Algebra.TensorProduct.map (AlgHom.id p.asIdeal.ResidueField p.asIdeal.ResidueField)
      (IsScalarTower.toAlgHom R A B)).Finite) :
    Algebra.QuasiFiniteAt A x.asIdeal := by
  let K := p.asIdeal.ResidueField
  let f := PrimeSpectrum.comap (algebraMap A B)
  let a := Algebra.TensorProduct.map (AlgHom.id K K) (IsScalarTower.toAlgHom R A B)
  let g := PrimeSpectrum.comap a.toRingHom
  let eB := PrimeSpectrum.preimageHomeomorphFiber R B p
  let eA := PrimeSpectrum.preimageHomeomorphFiber R A p
  let i := Subtype.val ∘ eB.symm
  let j := Subtype.val ∘ eA.symm
  have hi : IsEmbedding i := IsEmbedding.subtypeVal.comp eB.symm.isEmbedding
  have hj : Function.Injective j := Subtype.val_injective.comp eA.symm.injective
  have hcomm (t : PrimeSpectrum (K ⊗[R] B)) : f (i t) = j (g t) := by
    change (t.comap Algebra.TensorProduct.includeRight.toRingHom).comap (algebraMap A B) =
      (t.comap a.toRingHom).comap Algebra.TensorProduct.includeRight.toRingHom
    rw [← PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply]
    rfl
  let y := g (eB ⟨x, hx⟩)
  have hy : j y = f x := by
    rw [← hcomm]
    simp [i]
  have hset : i '' (g ⁻¹' {y}) = f ⁻¹' {f x} := by
    ext t
    constructor
    · rintro ⟨v, hv, rfl⟩
      change f (i v) = f x
      change g v = y at hv
      rw [hcomm, hv, hy]
    · intro ht
      change f t = f x at ht
      have ht' : t.comap (algebraMap R B) = p := by
        rw [IsScalarTower.algebraMap_eq R A B, PrimeSpectrum.comap_comp_apply]
        change (f t).comap (algebraMap R A) = p
        rw [ht]
        rw [IsScalarTower.algebraMap_eq R A B, PrimeSpectrum.comap_comp_apply] at hx
        exact hx
      let v := eB ⟨t, ht'⟩
      have hv : i v = t := by simp [i, v]
      refine ⟨v, hj ?_, hv⟩
      rw [← hcomm, hv, hy, ht]
  let : Algebra (K ⊗[R] A) (K ⊗[R] B) := a.toRingHom.toAlgebra
  let : Module.Finite (K ⊗[R] A) (K ⊗[R] B) := hfin
  have hdiscrete : _root_.IsDiscrete (f ⁻¹' {f x}) := by
    rw [← hset]
    exact (Algebra.QuasiFinite.isDiscrete_comap_preimage_singleton y).image hi.isInducing
  let : DiscreteTopology (f ⁻¹' {f x} : Set (PrimeSpectrum B)) :=
    isDiscrete_iff_discreteTopology.mp hdiscrete
  exact (Algebra.quasiFiniteAt_iff_isOpen_singleton_fiber x).mpr (isOpen_discrete _)

/--
概要：指定したファイバーの点の近くで、次元上限以下の変数を持つアフィン空間の
étale 近傍上に、有限で指定ファイバーが一点の部分を作れる。その近傍は相対次元が
変数の数に等しい滑らかなスキームを与える。
方針：不要な成分を主開で除いてから、ファイバー上の有限性と Zariski の主定理を使う。
規約：指定点は主開上のファイバー代数へ持ち上げる。
使われ方：次元を制御した相対 Noether 正規化。
-/
theorem exists_dim_le_etale_finite_piece_over_polynomial
    {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
    (p : Ideal R) [p.IsPrime] (z : Ideal (p.ResidueField ⊗[R] B)) [z.IsPrime]
    (d : WithBot ℕ∞)
    (hd : ∀ m ∈ minimalPrimes (p.ResidueField ⊗[R] B), m ≤ z →
      ringKrullDim ((p.ResidueField ⊗[R] B) ⧸ m) ≤ d) :
    ∃ a : B, ((1 : p.ResidueField) ⊗ₜ[R] a) ∉ z ∧
      ∃ n : ℕ, ∃ b : Fin n → Localization.Away a,
        ringKrullDim (p.ResidueField ⊗[R] Localization.Away a) = n ∧ (n : WithBot ℕ∞) ≤ d ∧
        let A := MvPolynomial (Fin n) R
        let L := Localization.Away a
        let φ := MvPolynomial.aeval (R := R) b
        letI : Algebra A L := φ.toRingHom.toAlgebra
        ∃ (x : Ideal L) (_ : x.IsPrime),
          x.comap (algebraMap B L) =
            z.comap (Algebra.TensorProduct.includeRight (R := R)).toRingHom ∧
          let q := x.comap φ.toRingHom
          letI : q.IsPrime := inferInstance
          ∃ (T : Type u) (_ : CommRing T) (_ : Algebra A T) (_ : Algebra.Etale A T)
            (y : Ideal T) (_ : y.IsPrime) (_ : y.LiesOver q)
            (e : T ⊗[A] L) (_ : IsIdempotentElem e)
            (w : Ideal (T ⊗[A] L)) (_ : w.IsPrime) (_ : w.LiesOver y),
            w.comap Algebra.TensorProduct.includeRight.toRingHom = x ∧ e ∉ w ∧
            Function.Bijective (Ideal.ResidueField.mapₐ q y (Algebra.ofId _ _) (y.over_def q)) ∧
            Module.Finite T (Localization.Away e) ∧
            SmoothOfRelativeDimension n
              (Spec.map (CommRingCat.ofHom ((algebraMap A T).comp (algebraMap R A)))) ∧
            ∀ w' : Ideal (T ⊗[A] L), w'.IsPrime → w'.LiesOver y → e ∉ w' → w' = w := by
  obtain ⟨a, ha, n, b, hdim, hn, _, hfin⟩ :=
    exists_fiber_noether_normalization_of_dim_le p z d hd
  let K := p.ResidueField
  let L := Localization.Away a
  let A := MvPolynomial (Fin n) R
  let φ : A →ₐ[R] L := MvPolynomial.aeval b
  let : Algebra A L := φ.toRingHom.toAlgebra
  let : IsScalarTower R A L := IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  let : Algebra.FiniteType R L := Algebra.FiniteType.trans ‹Algebra.FiniteType R B›
    (inferInstance : Algebra.FiniteType B L)
  let : Algebra.FiniteType A L := .of_restrictScalars_finiteType R A L
  let c := (1 : K) ⊗ₜ[R] a
  let l := IsLocalization.Away.tensorProductEquivTMulRight R K a L
  let loc := IsLocalization.primeSpectrumOrderIso (.powers c) (Localization.Away c)
  let t := loc.symm ⟨⟨z, inferInstance⟩, (Ideal.disjoint_powers_iff_notMem_of_isPrime c).mpr ha⟩
  let z' := t.comap l.toRingEquiv.toRingHom
  let eL := PrimeSpectrum.preimageHomeomorphFiber R L ⟨p, inferInstance⟩
  let x : PrimeSpectrum L := (eL.symm z').1
  have hx : x.comap (algebraMap R L) = ⟨p, inferInstance⟩ := (eL.symm z').2
  have hxz : x.asIdeal.comap (algebraMap B L) =
      z.comap (Algebra.TensorProduct.includeRight (R := R)).toRingHom := by
    ext r
    have ht : t.asIdeal.comap (algebraMap (K ⊗[R] B) (Localization.Away c)) = z :=
      congrArg (fun v => v.1.asIdeal) (loc.apply_symm_apply
        ⟨⟨z, inferInstance⟩, (Ideal.disjoint_powers_iff_notMem_of_isPrime c).mpr ha⟩)
    change l ((1 : K) ⊗ₜ[R] algebraMap B L r) ∈ t.asIdeal ↔ _
    rw [IsLocalization.Away.tensorProductEquivTMulRight_tmul]
    change (1 : K) ⊗ₜ[R] r ∈ t.asIdeal.comap _ ↔ _
    rw [ht]
    rfl
  let f := Algebra.TensorProduct.map (AlgHom.id K K) (IsScalarTower.toAlgHom R A L)
  let e := MvPolynomial.algebraTensorAlgEquiv (σ := Fin n) R K
  let g := MvPolynomial.aeval (R := K) (fun i => (1 : K) ⊗ₜ[R] b i)
  have hg : f.comp e.symm.toAlgHom = g := by
    refine MvPolynomial.algHom_ext fun i => ?_
    suffices (1 : K) ⊗ₜ[R] algebraMap A L (MvPolynomial.X i) = (1 : K) ⊗ₜ[R] b i by
      simpa [f, e, g, IsScalarTower.toAlgHom] using this
    exact congrArg (fun r : L => (1 : K) ⊗ₜ[R] r) (MvPolynomial.aeval_X (R := R) b i)
  have hf : f.Finite := by
    have heq : f = g.comp e.toAlgHom := by
      rw [← hg, AlgHom.comp_assoc]
      simp
    rw [heq]
    exact hfin.comp (AlgHom.Finite.of_surjective _ e.surjective)
  let : Algebra.QuasiFiniteAt A x.asIdeal :=
    quasiFiniteAt_of_finite_fiberMap ⟨p, inferInstance⟩ x hx hf
  let q := x.asIdeal.comap φ.toRingHom
  let : q.IsPrime := inferInstance
  let : x.asIdeal.LiesOver q := ⟨rfl⟩
  obtain ⟨T, _, _, hEtale, y, hy, hlo, e, he, w, hw, hwy, hwx, hwe, hκ, hfinite, huniq⟩ :=
    Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq q x.asIdeal
  let fA := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let fT := Spec.map (CommRingCat.ofHom (algebraMap A T))
  let : SmoothOfRelativeDimension n fA := by
    apply (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)).mpr
    apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
    change (algebraMap R A).IsStandardSmoothOfRelativeDimension n
    rw [RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
    infer_instance
  let : Etale fT := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    (RingHom.etale_algebraMap.mpr inferInstance)
  have hsmooth : SmoothOfRelativeDimension n (fT ≫ fA) := by
    simpa only [zero_add] using
      (inferInstance : SmoothOfRelativeDimension (0 + n) (fT ≫ fA))
  refine ⟨a, ha, n, b, hdim, hn, x.asIdeal, x.2, hxz, T, _, _, hEtale, y, hy, hlo,
    e, he, w, hw, hwy, hwx, hwe, hκ, hfinite, ?_, huniq⟩
  rwa [CommRingCat.ofHom_comp, Spec.map_comp]

end SerrePositivity.AlgebraicGeometry
