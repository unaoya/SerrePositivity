module

public import SerrePositivity.AlgebraicGeometry.FiberPrimeDimension
public import Mathlib.RingTheory.Etale.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
概要：次元と剰余体を制御した一つの正規化写像を étale 局所有限化に渡す。
方針：剰余体への底変換での有限性を使って準有限性を示し、指定ファイバーを一点に分離する。
規約：剰余体の同型は元の基底環上の代数同型で表す。
使われ方：滑らかな相対正規化先の幾何学的整な成分を選ぶ。
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
概要：指定点の近くで、次元上限以下の滑らかなアフィン基底への有限写像を étale 局所で作り、
同じ基底の指定点の剰余体を有理関数体にできる。
方針：剰余体を制御した正規化写像を、剰余体を保存する étale 近傍で局所有限化する。
規約：相対次元は指定点を残した主開のファイバーの次元に等しい。
使われ方：Stacks 052E のアフィンの場合と、057S の滑らかな基底を選ぶ段階。
-/
theorem exists_dim_le_etale_finite_piece_with_rational_residue
    {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
    (p : Ideal R) [p.IsPrime] (z : Ideal (p.ResidueField ⊗[R] B)) [z.IsPrime]
    (d : WithBot ℕ∞)
    (hd : ∀ m ∈ minimalPrimes (p.ResidueField ⊗[R] B), m ≤ z →
      ringKrullDim ((p.ResidueField ⊗[R] B) ⧸ m) ≤ d) :
    ∃ a : B, ((1 : p.ResidueField) ⊗ₜ[R] a) ∉ z ∧
      ∃ n : ℕ, ∃ b : Fin n → Localization.Away a, ∃ r : ℕ,
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
            letI : Algebra R T := ((algebraMap A T).comp (algebraMap R A)).toAlgebra
            Nonempty (y.ResidueField ≃ₐ[R] FractionRing (MvPolynomial (Fin r) p.ResidueField)) ∧
            Module.Finite T (Localization.Away e) ∧
            SmoothOfRelativeDimension n
              (Spec.map (CommRingCat.ofHom ((algebraMap A T).comp (algebraMap R A)))) ∧
            ∀ w' : Ideal (T ⊗[A] L), w'.IsPrime → w'.LiesOver y → e ∉ w' → w' = w := by
  obtain ⟨a, ha, n, b, r, hdim, hn, x, hx, hxz, hfin, ⟨hres⟩⟩ :=
    exists_fiber_prime_normalization_of_dim_le p z d hd
  let L := Localization.Away a
  let A := MvPolynomial (Fin n) R
  let φ : A →ₐ[R] L := MvPolynomial.aeval b
  let : Algebra A L := φ.toRingHom.toAlgebra
  let : IsScalarTower R A L := IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  let : Algebra.FiniteType R L := Algebra.FiniteType.trans ‹Algebra.FiniteType R B›
    (inferInstance : Algebra.FiniteType B L)
  let : Algebra.FiniteType A L := .of_restrictScalars_finiteType R A L
  let P : PrimeSpectrum R := ⟨p, inferInstance⟩
  have hz : ((⟨z, inferInstance⟩ : PrimeSpectrum (p.ResidueField ⊗[R] B)).comap
      (Algebra.TensorProduct.includeRight (R := R)).toRingHom).comap (algebraMap R B) = P :=
    ((PrimeSpectrum.preimageHomeomorphFiber R B P).symm ⟨z, inferInstance⟩).2
  have hxz' : (⟨x, hx⟩ : PrimeSpectrum L).comap (algebraMap B L) =
      (⟨z, inferInstance⟩ : PrimeSpectrum (p.ResidueField ⊗[R] B)).comap
        (Algebra.TensorProduct.includeRight (R := R)).toRingHom :=
    PrimeSpectrum.ext hxz
  have hxp : (⟨x, hx⟩ : PrimeSpectrum L).comap (algebraMap R L) = P := by
    rwa [IsScalarTower.algebraMap_eq R B L, PrimeSpectrum.comap_comp_apply, hxz']
  have hmap : IsScalarTower.toAlgHom R A L = φ := AlgHom.ext fun _ => rfl
  let : Algebra.QuasiFiniteAt A x :=
    quasiFiniteAt_of_finite_fiberMap P ⟨x, hx⟩ hxp (hmap.symm ▸ hfin)
  let q := x.comap φ.toRingHom
  let : q.IsPrime := inferInstance
  let : x.LiesOver q := ⟨rfl⟩
  obtain ⟨T, _, _, hEtale, y, hy, hlo, e, he, w, hw, hwy, hwx, hwe, hκ, hfinite, huniq⟩ :=
    Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq q x
  let : Algebra R T := ((algebraMap A T).comp (algebraMap R A)).toAlgebra
  let : IsScalarTower R A T := IsScalarTower.of_algebraMap_eq' rfl
  let κmap := Ideal.ResidueField.mapₐ q y (IsScalarTower.toAlgHom R A T) (y.over_def q)
  have hκ' : Function.Bijective κmap := hκ
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
  refine ⟨a, ha, n, b, r, hdim, hn, x, hx, hxz, T, _, _, hEtale, y, hy, hlo,
    e, he, w, hw, hwy, hwx, hwe, ⟨(AlgEquiv.ofBijective κmap hκ').symm.trans hres⟩,
    hfinite, ?_, huniq⟩
  rwa [CommRingCat.ofHom_comp, Spec.map_comp]

end SerrePositivity.AlgebraicGeometry
