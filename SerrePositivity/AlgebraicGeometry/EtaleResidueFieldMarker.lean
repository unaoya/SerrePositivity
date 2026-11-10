module

public import SerrePositivity.AlgebraicGeometry.EtaleFiniteFlatMarker
public import SerrePositivity.AlgebraicGeometry.EtalePolynomialMarker
public import SerrePositivity.AlgebraicGeometry.ResidueFieldIntegralCoordinates

/-!
概要：剰余体の有限拡大に値を取る点から、基底の初等 étale 近傍で有限平坦な標識を作る。
方針：座標の分母を払い、平坦な準有限切断を作って、指定ファイバーの有限部分を分離する。
規約：始域は多項式代数上 étale とする。
使われ方：相対 Noether 正規化先の指定ファイバーを幾何学的整な開部分に広げる。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open scoped TensorProduct

/--
概要：多項式代数上の étale チャートの剰余体代数に値を取る点は、
元の基底上平坦かつ準有限な標識を経由する。
方針：モニック方程式を定義できる主開で有限自由な座標切断を作り、étale チャートへ引き戻す。
規約：点の座標は指定した剰余体上で整とする。
使われ方：初等 étale 近傍上で有限射影な標識を取り出す。
-/
theorem exists_flat_quasiFinite_marker_of_integral_residueField
    {R B F : Type u} [CommRing R] [CommRing B] [Field F] [Algebra R B]
    (p : Ideal R) [p.IsPrime] [Algebra R F] [Algebra p.ResidueField F]
    [IsScalarTower R p.ResidueField F] {n : ℕ}
    [Algebra (MvPolynomial (Fin n) R) B] [IsScalarTower R (MvPolynomial (Fin n) R) B]
    [Algebra.Etale (MvPolynomial (Fin n) R) B] (y : B →ₐ[R] F)
    (hy : ∀ i : Fin n,
      IsIntegral p.ResidueField (y (algebraMap (MvPolynomial (Fin n) R) B (MvPolynomial.X i)))) :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra R D) (_ : Algebra.FiniteType R D)
      (_ : Module.Flat R D) (_ : Algebra.QuasiFinite R D)
      (i : B →ₐ[R] D) (z : D →ₐ[R] F), z.comp i = y := by
  let P := MvPolynomial (Fin n) R
  let x (i : Fin n) := y (algebraMap P B (MvPolynomial.X i))
  obtain ⟨a, _, j, hj⟩ := exists_away_integral_of_isIntegral_residueField p x hy
  let A := Localization.Away a
  let : Algebra A F := j.toRingHom.toAlgebra
  let : IsScalarTower R A F := IsScalarTower.of_algebraMap_eq' j.comp_algebraMap.symm
  obtain ⟨C, _, _, _, _, φA, ψA, _, hψ⟩ :=
    exists_finiteFree_quotient_of_integral_coordinates (R := A) x hj
  let : Algebra R C := ((algebraMap A C).comp (algebraMap R A)).toAlgebra
  let : IsScalarTower R A C := IsScalarTower.of_algebraMap_eq' rfl
  let φ : P →ₐ[R] C := MvPolynomial.aeval fun i => φA (MvPolynomial.X i)
  let ψ : C →ₐ[R] F := ψA.restrictScalars R
  have hP : y.comp (IsScalarTower.toAlgHom R P B) = ψ.comp φ := by
    apply MvPolynomial.algHom_ext
    intro i
    have h := DFunLike.congr_fun hψ (MvPolynomial.X i)
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X] at h
    change x i = ψ (φ (MvPolynomial.X i))
    rw [show φ (MvPolynomial.X i) = φA (MvPolynomial.X i) from MvPolynomial.aeval_X _ _]
    exact h.symm
  let : Algebra P C := φ.toRingHom.toAlgebra
  let : IsScalarTower R P C := IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  let : Algebra C F := ψ.toRingHom.toAlgebra
  let : IsScalarTower R C F := IsScalarTower.of_algebraMap_eq' ψ.comp_algebraMap.symm
  let : Algebra P F := (ψ.comp φ).toRingHom.toAlgebra
  let : IsScalarTower P C F := IsScalarTower.of_algebraMap_eq' rfl
  let D := C ⊗[P] B
  let : Algebra.FiniteType R C := .trans (inferInstance : Algebra.FiniteType R A)
    (inferInstance : Algebra.FiniteType A C)
  let : Algebra.FiniteType R D := .trans (inferInstance : Algebra.FiniteType R C)
    (inferInstance : Algebra.FiniteType C D)
  let : Module.Flat R C := Module.Flat.trans R A C
  let : Module.Flat R D := Module.Flat.trans R C D
  let : Algebra.QuasiFinite R A := Algebra.QuasiFinite.of_isLocalization (.powers a)
  let : Algebra.QuasiFinite R C := Algebra.QuasiFinite.trans R A C
  let : Algebra.QuasiFinite R D := Algebra.QuasiFinite.trans R C D
  let y' : B →ₐ[P] F := ⟨y.toRingHom, DFunLike.congr_fun hP⟩
  let z : D →ₐ[C] F :=
    Algebra.TensorProduct.lift (Algebra.ofId C F) y' fun _ _ => .all _ _
  refine ⟨D, _, _, inferInstance, inferInstance, inferInstance,
    Algebra.TensorProduct.includeRight.restrictScalars R, z.restrictScalars R, ?_⟩
  ext b
  change z (1 ⊗ₜ[P] b) = y' b
  simpa only [map_one, one_mul] using
    Algebra.TensorProduct.lift_tmul (Algebra.ofId C F) y' (fun _ _ => .all _ _) (1 : C) b

/--
概要：剰余体上で座標が整な étale チャートの点があれば、その基底の初等 étale 近傍で、
指定ファイバーと交わる有限射影な標識が存在する。
方針：平坦な準有限切断の指定点を、剰余体を保存する étale 近傍上の有限部分に分離する。
規約：標識は底変換したチャートの座標環からの代数準同型で与える。
使われ方：Stacks 057J の滑らかな正規化先における標識の構成。
-/
theorem exists_etale_finiteProjective_marker_of_integral_residueField
    {R B F : Type u} [CommRing R] [IsNoetherianRing R] [CommRing B] [Field F] [Algebra R B]
    (p : Ideal R) [p.IsPrime] [Algebra R F] [Algebra p.ResidueField F]
    [IsScalarTower R p.ResidueField F] {n : ℕ}
    [Algebra (MvPolynomial (Fin n) R) B] [IsScalarTower R (MvPolynomial (Fin n) R) B]
    [Algebra.Etale (MvPolynomial (Fin n) R) B] (y : B →ₐ[R] F)
    (hy : ∀ i : Fin n,
      IsIntegral p.ResidueField (y (algebraMap (MvPolynomial (Fin n) R) B (MvPolynomial.X i)))) :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T) (_ : Algebra.Etale R T)
      (s : Ideal T) (_ : s.IsPrime) (_ : s.LiesOver p),
      Function.Bijective (Ideal.ResidueField.mapₐ p s (Algebra.ofId R T) (s.over_def p)) ∧
      ∃ (M : Type u) (_ : CommRing M) (_ : Algebra T M) (_ : Module.Finite T M)
        (_ : Module.Projective T M), Nonempty (T ⊗[R] B →ₐ[T] M) ∧
        ∃ m : PrimeSpectrum M, m.asIdeal.comap (algebraMap T M) = s := by
  obtain ⟨D, _, _, _, _, _, i, z, _⟩ :=
    exists_flat_quasiFinite_marker_of_integral_residueField p y hy
  let q := RingHom.ker z.toRingHom
  let : q.IsPrime := RingHom.ker_isPrime z.toRingHom
  let : q.LiesOver p := ⟨by
    change p = (RingHom.ker z.toRingHom).comap (algebraMap R D)
    have hz : z.toRingHom.comp (algebraMap R D) = algebraMap R F := RingHom.ext z.commutes
    rw [RingHom.comap_ker, hz, IsScalarTower.algebraMap_eq R p.ResidueField F,
      RingHom.ker_comp_of_injective _ (RingHom.injective _), Ideal.ker_algebraMap_residueField]⟩
  let : Algebra.QuasiFiniteAt R q := Algebra.QuasiFinite.of_isLocalization q.primeCompl
  obtain ⟨T, _, _, _, s, _, _, e, _, w, _, _, _, hew, hs, hfin, hproj, _⟩ :=
    exists_etale_finiteProjective_piece_at_quasiFinite p q
  let E := T ⊗[R] D
  let M := Localization.Away e
  let σ : T ⊗[R] B →ₐ[T] M :=
    (IsScalarTower.toAlgHom T E M).comp (Algebra.TensorProduct.map (AlgHom.id T T) i)
  let l := IsLocalization.primeSpectrumOrderIso (.powers e) M
  let v : {x : PrimeSpectrum E // Disjoint (Submonoid.powers e : Set E) x.asIdeal} :=
    ⟨⟨w, inferInstance⟩, (Ideal.disjoint_powers_iff_notMem_of_isPrime e).mpr hew⟩
  let m := l.symm v
  have hm : m.asIdeal.comap (algebraMap E M) = w :=
    congrArg (fun x => x.1.asIdeal) (l.apply_symm_apply v)
  refine ⟨T, _, _, inferInstance, s, inferInstance, inferInstance, hs,
    M, _, _, hfin, hproj, ⟨σ⟩, m, ?_⟩
  rw [IsScalarTower.algebraMap_eq T E M, ← Ideal.comap_comap, hm]
  exact (w.over_def s).symm

end SerrePositivity.AlgebraicGeometry
