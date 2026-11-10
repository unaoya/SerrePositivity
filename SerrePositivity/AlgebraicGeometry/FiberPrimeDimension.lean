module

public import SerrePositivity.AlgebraicGeometry.FiberDimensionBound
public import SerrePositivity.AlgebraicGeometry.PolynomialPrimeNormalization
import Mathlib.RingTheory.Localization.BaseChange

/-!
概要：同じ多項式写像でファイバーの次元と指定点の像の剰余体を制御する。
方針：主開で次元を抑えてから、変数の数を固定したまま素イデアルを座標イデアルに移す。
規約：剰余体の同型は元の基底環上の代数同型として与える。
使われ方：幾何学的整な成分を広げるための、相対 Noether 正規化の入力。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open scoped TensorProduct

private theorem exists_fiber_coordinate_quotient
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    (p : Ideal R) [p.IsPrime] (z : Ideal (p.ResidueField ⊗[R] B)) [z.IsPrime]
    {n : ℕ} (f : MvPolynomial (Fin n) p.ResidueField →ₐ[p.ResidueField] p.ResidueField ⊗[R] B)
    (hf : f.Finite) :
    ∃ b : Fin n → B, ∃ r : ℕ,
      let g := MvPolynomial.aeval (R := p.ResidueField)
        (fun i => (1 : p.ResidueField) ⊗ₜ[R] b i)
      g.Finite ∧ Nonempty ((MvPolynomial (Fin n) p.ResidueField ⧸ z.comap g.toRingHom)
        ≃ₐ[p.ResidueField] MvPolynomial (Fin r) p.ResidueField) := by
  let K := p.ResidueField
  let q := z.comap f.toRingHom
  let : q.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨r, φ, δ, hφ, hδ, hker, _, _⟩ := exists_finite_endomorphism_comap_eq_coordinate_ker q
  let P := MvPolynomial (Fin n) K
  let g := f.comp φ
  choose s b hs hb using fun i : Fin n => exists_fiber_denominator p (g (MvPolynomial.X i))
  let d (i : Fin n) := algebraMap R K (s i)
  have hd (i : Fin n) : d i ≠ 0 := fun h => hs i (Ideal.algebraMap_residueField_eq_zero.mp h)
  let σ : P →ₐ[K] P := MvPolynomial.aeval fun i => d i • MvPolynomial.X i
  let τ : P →ₐ[K] P := MvPolynomial.aeval fun i => (d i)⁻¹ • MvPolynomial.X i
  have hσX (i : Fin n) : σ (MvPolynomial.X i) = d i • MvPolynomial.X i :=
    MvPolynomial.aeval_X _ i
  have hστ : σ.comp τ = AlgHom.id K P := by
    refine MvPolynomial.algHom_ext fun i => ?_
    change σ (τ (MvPolynomial.X i)) = MvPolynomial.X i
    have hτX : τ (MvPolynomial.X i) = (d i)⁻¹ • MvPolynomial.X i := MvPolynomial.aeval_X _ i
    rw [hτX, map_smul, hσX, smul_smul, inv_mul_cancel₀ (hd i), one_smul]
  have hσ : Function.Surjective σ :=
    Function.RightInverse.surjective (g := τ) fun y => DFunLike.congr_fun hστ y
  have he : MvPolynomial.aeval (R := K) (fun i => (1 : K) ⊗ₜ[R] b i) = g.comp σ := by
    refine MvPolynomial.algHom_ext fun i => ?_
    change MvPolynomial.aeval (R := K) (fun j => (1 : K) ⊗ₜ[R] b j) (MvPolynomial.X i) =
      g (σ (MvPolynomial.X i))
    rw [MvPolynomial.aeval_X, hσX, map_smul]
    exact (hb i).symm
  refine ⟨b, r, ?_⟩
  dsimp only
  rw [he]
  refine ⟨(hf.comp hφ).comp (AlgHom.Finite.of_surjective _ hσ), ?_⟩
  have hker' : z.comap (g.comp σ).toRingHom = RingHom.ker (δ.comp σ).toRingHom := by
    ext a
    change σ a ∈ q.comap φ.toRingHom ↔ σ a ∈ RingHom.ker δ.toRingHom
    rw [hker]
  rw [hker']
  exact ⟨Ideal.quotientKerAlgEquivOfSurjective (hδ.comp hσ)⟩

private theorem fiber_coordinate_quotient_baseChange
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    (p : Ideal R) [p.IsPrime] (z : Ideal (p.ResidueField ⊗[R] B)) [z.IsPrime]
    {n r : ℕ} (b : Fin n → B)
    (hfin : (MvPolynomial.aeval (R := p.ResidueField)
      (fun i => (1 : p.ResidueField) ⊗ₜ[R] b i)).Finite)
    (hquot : (MvPolynomial (Fin n) p.ResidueField ⧸ z.comap (MvPolynomial.aeval
      (R := p.ResidueField) (fun i => (1 : p.ResidueField) ⊗ₜ[R] b i)).toRingHom)
        ≃ₐ[p.ResidueField] MvPolynomial (Fin r) p.ResidueField) :
    let φ := MvPolynomial.aeval (R := R) b
    let q := (z.comap Algebra.TensorProduct.includeRight.toRingHom).comap φ.toRingHom
    letI : q.IsPrime := inferInstance
    (Algebra.TensorProduct.map (AlgHom.id p.ResidueField p.ResidueField) φ).Finite ∧
      Nonempty (q.ResidueField ≃ₐ[R] FractionRing (MvPolynomial (Fin r) p.ResidueField)) := by
  let K := p.ResidueField
  let A := MvPolynomial (Fin n) R
  let P := MvPolynomial (Fin n) K
  let φ : A →ₐ[R] B := MvPolynomial.aeval b
  let a := Algebra.TensorProduct.map (AlgHom.id K K) φ
  let e := MvPolynomial.algebraTensorAlgEquiv (σ := Fin n) R K
  let g : P →ₐ[K] K ⊗[R] B := MvPolynomial.aeval (fun i => (1 : K) ⊗ₜ[R] b i)
  have h : a.comp e.symm.toAlgHom = g := by
    refine MvPolynomial.algHom_ext fun i => ?_
    suffices (1 : K) ⊗ₜ[R] φ (MvPolynomial.X i) = (1 : K) ⊗ₜ[R] b i by
      simpa [a, e, g, φ] using this
    exact congrArg (fun x : B => (1 : K) ⊗ₜ[R] x) (MvPolynomial.aeval_X (R := R) b i)
  have ha : a = g.comp e.toAlgHom := by
    rw [← h, AlgHom.comp_assoc]
    simp
  let iA : A →ₐ[R] K ⊗[R] A := Algebra.TensorProduct.includeRight
  let iB : B →ₐ[R] K ⊗[R] B := Algebra.TensorProduct.includeRight
  let i : A →ₐ[R] P := (e.toAlgHom.restrictScalars R).comp iA
  let q := (z.comap iB.toRingHom).comap φ.toRingHom
  let qK := z.comap g.toRingHom
  let : q.IsPrime := inferInstance
  let : qK.IsPrime := inferInstance
  have hcomm : (g.restrictScalars R).comp i = iB.comp φ := by
    change (g.restrictScalars R).comp ((e.toAlgHom.restrictScalars R).comp iA) = _
    rw [← AlgHom.comp_assoc]
    change ((g.comp e.toAlgHom).restrictScalars R).comp iA = _
    rw [← ha]
    ext x
    rfl
  have hq : q = qK.comap i.toRingHom := by
    ext x
    change iB (φ x) ∈ z ↔ g (i x) ∈ z
    exact (DFunLike.congr_fun hcomm x).symm ▸ Iff.rfl
  have hiA : iA.toRingHom.SurjectiveOnStalks :=
    (Ideal.surjectiveOnStalks_residueField p).baseChange'
  have hi : i.toRingHom.SurjectiveOnStalks :=
    e.toRingEquiv.surjectiveOnStalks.comp hiA
  let j := Ideal.ResidueField.mapₐ q qK i hq
  have hj : Function.Bijective j := hi.residueFieldMap_bijective q qK hq
  have hfield : qK.ResidueField ≃ₐ[K] FractionRing (MvPolynomial (Fin r) K) :=
    IsFractionRing.algEquivOfAlgEquiv hquot
  refine ⟨?_, ⟨(AlgEquiv.ofBijective j hj).trans (hfield.restrictScalars R)⟩⟩
  change a.Finite
  rw [ha]
  exact hfin.comp (AlgHom.Finite.of_surjective _ e.surjective)


/--
概要：指定点を残す主開で、アフィン空間の変数の数をファイバーの次元に合わせ、
同じ写像について指定点の像の剰余体を有理関数体にできる。
方針：次元付き正規化の後、同じ数の変数の有限自己写像を合成して分母を払う。
規約：元の多項式写像の有限性は剰余体への基底変更後に主張する。
使われ方：次元と剰余体をともに制御した相対 Noether 正規化。
-/
theorem exists_fiber_prime_normalization_of_dim_le
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
    (p : Ideal R) [p.IsPrime] (z : Ideal (p.ResidueField ⊗[R] B)) [z.IsPrime]
    (d : WithBot ℕ∞)
    (hd : ∀ m ∈ minimalPrimes (p.ResidueField ⊗[R] B), m ≤ z →
      ringKrullDim ((p.ResidueField ⊗[R] B) ⧸ m) ≤ d) :
    ∃ a : B, ((1 : p.ResidueField) ⊗ₜ[R] a) ∉ z ∧
      ∃ n : ℕ, ∃ b : Fin n → Localization.Away a, ∃ r : ℕ,
        ringKrullDim (p.ResidueField ⊗[R] Localization.Away a) = n ∧ (n : WithBot ℕ∞) ≤ d ∧
        ∃ (x : Ideal (Localization.Away a)) (_ : x.IsPrime),
          x.comap (algebraMap B (Localization.Away a)) =
            z.comap (Algebra.TensorProduct.includeRight (R := R)).toRingHom ∧
          let φ := MvPolynomial.aeval (R := R) b
          let q := x.comap φ.toRingHom
          letI : q.IsPrime := inferInstance
          (Algebra.TensorProduct.map (AlgHom.id p.ResidueField p.ResidueField) φ).Finite ∧
            Nonempty (q.ResidueField ≃ₐ[R] FractionRing (MvPolynomial (Fin r) p.ResidueField)) := by
  obtain ⟨a, ha, n, b, hdim, hn, _, hfin⟩ :=
    exists_fiber_noether_normalization_of_dim_le p z d hd
  let K := p.ResidueField
  let L := Localization.Away a
  let c := (1 : K) ⊗ₜ[R] a
  let l := IsLocalization.Away.tensorProductEquivTMulRight R K a L
  let loc := IsLocalization.primeSpectrumOrderIso (.powers c) (Localization.Away c)
  let t := loc.symm ⟨⟨z, inferInstance⟩, (Ideal.disjoint_powers_iff_notMem_of_isPrime c).mpr ha⟩
  let z' := t.comap l.toRingEquiv.toRingHom
  let x := z'.asIdeal.comap (Algebra.TensorProduct.includeRight (R := R)).toRingHom
  have hxz : x.comap (algebraMap B L) =
      z.comap (Algebra.TensorProduct.includeRight (R := R)).toRingHom := by
    ext s
    have ht : t.asIdeal.comap (algebraMap (K ⊗[R] B) (Localization.Away c)) = z :=
      congrArg (fun v => v.1.asIdeal) (loc.apply_symm_apply
        ⟨⟨z, inferInstance⟩, (Ideal.disjoint_powers_iff_notMem_of_isPrime c).mpr ha⟩)
    change l ((1 : K) ⊗ₜ[R] algebraMap B L s) ∈ t.asIdeal ↔ _
    rw [IsLocalization.Away.tensorProductEquivTMulRight_tmul]
    change (1 : K) ⊗ₜ[R] s ∈ t.asIdeal.comap _ ↔ _
    rw [ht]
    rfl
  let g := MvPolynomial.aeval (R := K) (fun i => (1 : K) ⊗ₜ[R] b i)
  obtain ⟨b', r, hfin', ⟨hquot⟩⟩ := exists_fiber_coordinate_quotient p z'.asIdeal g hfin
  exact ⟨a, ha, n, b', r, hdim, hn, x, inferInstance, hxz,
    fiber_coordinate_quotient_baseChange p z'.asIdeal b' hfin' hquot⟩

end SerrePositivity.AlgebraicGeometry
