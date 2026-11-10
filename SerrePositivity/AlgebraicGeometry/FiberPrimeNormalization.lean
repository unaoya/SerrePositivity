module

public import SerrePositivity.AlgebraicGeometry.FiberNoetherNormalization
public import SerrePositivity.AlgebraicGeometry.PolynomialPrimeNormalization

/-!
概要：指定したファイバーの点を、多項式環の座標部分空間の生成点に送る。
方針：ファイバーでの正規化を有限自己写像と合成し、変数ごとに分母を払う。
規約：像の点が定める整域を、剰余体上の多項式代数との同型で表す。
使われ方：相対 Noether 正規化の étale 局所有限化で、像の点の剰余体を制御する。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open scoped TensorProduct

/--
概要：指定したアフィンファイバーの素イデアルに対し、元の代数の元で選んだ有限な
多項式評価写像で、逆像による商が剰余体上の多項式環になるものがある。
方針：Noether 正規化の後で逆像を座標イデアルにし、分母を払う変数のスカラー倍を
多項式環の自己同型として商の表示に組み込む。
規約：有限性と商の表示はともにファイバー上で主張する。
使われ方：相対 Noether 正規化における像の点の剰余体の計算。
-/
theorem exists_fiber_prime_normalization
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
    (p : Ideal R) [p.IsPrime] (z : Ideal (p.ResidueField ⊗[R] B)) [z.IsPrime] :
    ∃ n : ℕ, ∃ b : Fin n → B, ∃ r : ℕ,
      let g := MvPolynomial.aeval (R := p.ResidueField)
        (fun i => (1 : p.ResidueField) ⊗ₜ[R] b i)
      g.Finite ∧ Nonempty ((MvPolynomial (Fin n) p.ResidueField ⧸ z.comap g.toRingHom)
        ≃ₐ[p.ResidueField] MvPolynomial (Fin r) p.ResidueField) := by
  let K := p.ResidueField
  let : Nontrivial (K ⊗[R] B) :=
    PrimeSpectrum.nonempty_iff_nontrivial.mp ⟨⟨z, inferInstance⟩⟩
  obtain ⟨n, f, _, hf⟩ := exists_finite_inj_algHom_of_fg K (K ⊗[R] B)
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
  refine ⟨n, b, r, ?_⟩
  dsimp only
  rw [he]
  refine ⟨(hf.comp hφ).comp (AlgHom.Finite.of_surjective _ hσ), ?_⟩
  have hker' : z.comap (g.comp σ).toRingHom = RingHom.ker (δ.comp σ).toRingHom := by
    ext a
    change σ a ∈ q.comap φ.toRingHom ↔ σ a ∈ RingHom.ker δ.toRingHom
    rw [hker]
  rw [hker']
  exact ⟨Ideal.quotientKerAlgEquivOfSurjective (hδ.comp hσ)⟩

/--
概要：元のアフィン射から多項式環への射を選び、ファイバーでは有限、指定点の像では
剰余体が基底点の剰余体上の有理関数体となるようにできる。
方針：ファイバーでの多項式商の同型を分数体に移し、ファイバーへの制限が
剰余体を変えないことを使う。
規約：剰余体の同型は、元の基底環上の代数同型で表す。
使われ方：相対 Noether 正規化の有限な étale 局所部分に剰余体の情報を渡す。
-/
theorem exists_fiber_prime_normalization_baseChange
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
    (p : Ideal R) [p.IsPrime] (z : Ideal (p.ResidueField ⊗[R] B)) [z.IsPrime] :
    ∃ n : ℕ, ∃ b : Fin n → B, ∃ r : ℕ,
      let φ := MvPolynomial.aeval (R := R) b
      let q := (z.comap Algebra.TensorProduct.includeRight.toRingHom).comap φ.toRingHom
      letI : q.IsPrime := inferInstance
      (Algebra.TensorProduct.map (AlgHom.id p.ResidueField p.ResidueField) φ).Finite ∧
        Nonempty (q.ResidueField ≃ₐ[R] FractionRing (MvPolynomial (Fin r) p.ResidueField)) := by
  obtain ⟨n, b, r, hfin, ⟨hquot⟩⟩ := exists_fiber_prime_normalization p z
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
  refine ⟨n, b, r, ?_, ⟨(AlgEquiv.ofBijective j hj).trans (hfield.restrictScalars R)⟩⟩
  change a.Finite
  rw [ha]
  exact hfin.comp (AlgHom.Finite.of_surjective _ e.surjective)

end SerrePositivity.AlgebraicGeometry
