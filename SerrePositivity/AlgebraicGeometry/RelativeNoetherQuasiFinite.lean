module

public import SerrePositivity.AlgebraicGeometry.FiberNoetherNormalization
public import SerrePositivity.AlgebraicGeometry.QuasiFiniteFiberComparison
public import Mathlib.RingTheory.Etale.QuasiFinite

/-!
概要：指定したファイバーの各点で準有限となる、アフィン空間への写像を選ぶ。
方針：剰余体上で有限となる多項式評価写像から、元の写像の準有限性を得る。
規約：元の写像の準有限性は、選んだ基底点のファイバー上で主張する。
使われ方：相対 Noether 正規化の étale 局所有限化を Zariski の主定理に渡す。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false in
private theorem fiber_projection_spec
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] (p : Spec (.of R)) :
    let i := Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight (R := R) (A := p.asIdeal.ResidueField)
        (B := A)).toRingHom)
    IsPreimmersion i ∧ Set.range i =
      (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⁻¹' {p} := by
  let K := p.asIdeal.ResidueField
  let k := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let f := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let e := pullbackSpecIso R K A
  have hk : IsPreimmersion k := by
    let j := Spec.map (Scheme.Spec.residueFieldIso (CommRingCat.of R) p).inv
    have hj : j ≫ k = (Spec (.of R)).fromSpecResidueField p :=
      Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField (.of R) p
    exact (MorphismProperty.cancel_left_of_respectsIso @IsPreimmersion j k).mp
      (hj ▸ inferInstance)
  let i := Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight (R := R) (A := K) (B := A)).toRingHom)
  have hi : e.inv ≫ pullback.snd k f = i := pullbackSpecIso_inv_snd R K A
  change IsPreimmersion i ∧ Set.range i = f ⁻¹' {p}
  rw [← hi]
  refine ⟨inferInstance, ?_⟩
  change Set.range ((pullback.snd k f) ∘ e.inv) = f ⁻¹' {p}
  rw [e.inv.surjective.range_comp, Scheme.Pullback.range_snd]
  exact congrArg (fun s => f ⁻¹' s) (PrimeSpectrum.residueField_comap p)

set_option backward.isDefEq.respectTransparency false in
/--
概要：有限型のアフィン射と非空なファイバーに対し、そのファイバーの全点で準有限な
多項式評価写像が存在する。
方針：剰余体に移すと評価写像は有限であり、そのファイバーの離散性を元の写像へ移す。
規約：変数は元の代数の元で選び、評価写像の始域は基底上の多項式環。
使われ方：指定点の近くでの étale 局所有限化。
-/
theorem exists_polynomial_quasiFiniteAt_on_fiber
    {R B : Type u} [CommRing R] [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
    (p : Spec (.of R)) [Nontrivial (p.asIdeal.ResidueField ⊗[R] B)] :
    ∃ n : ℕ, ∃ b : Fin n → B,
      let f := Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := R) b).toRingHom)
      LocallyOfFiniteType f ∧ ∀ x : Spec (.of B),
        Spec.map (CommRingCat.ofHom (algebraMap R B)) x = p → f.QuasiFiniteAt x := by
  obtain ⟨n, b, _, hfin⟩ :=
    exists_fiber_noether_normalization_baseChange (B := B) p.asIdeal
  let A := MvPolynomial (Fin n) R
  let K := p.asIdeal.ResidueField
  let φ : A →ₐ[R] B := MvPolynomial.aeval b
  let f := Spec.map (CommRingCat.ofHom φ.toRingHom)
  have htype : φ.toRingHom.FiniteType := by
    have h : (φ.toRingHom.comp (algebraMap R A)).FiniteType := by
      have heq : φ.toRingHom.comp (algebraMap R A) = algebraMap R B := φ.comp_algebraMap
      exact heq.symm ▸ (RingHom.finiteType_algebraMap.mpr inferInstance)
    exact h.of_comp_finiteType
  have : LocallyOfFiniteType f := HasRingHomProperty.Spec_iff.mpr htype
  let a := Algebra.TensorProduct.map (AlgHom.id K K) φ
  let g := Spec.map (CommRingCat.ofHom a.toRingHom)
  have : IsFinite g := (IsFinite.SpecMap_iff _).mpr hfin
  let i := Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight (R := R) (A := K) (B := B)).toRingHom)
  let j := Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight (R := R) (A := K) (B := A)).toRingHom)
  obtain ⟨hi, hirange⟩ := fiber_projection_spec R B p
  obtain ⟨hj, hjrange⟩ := fiber_projection_spec R A p
  have hcomm : i ≫ f = g ≫ j := by
    dsimp only [i, f, g, j]
    rw [← Spec.map_comp, ← Spec.map_comp]; rfl
  let fA := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let fB := Spec.map (CommRingCat.ofHom (algebraMap R B))
  have hbase : f ≫ fA = fB := by
    dsimp only [f, fA, fB]
    rw [← Spec.map_comp]
    congr 1
    ext r
    exact φ.commutes r
  refine ⟨n, b, ‹LocallyOfFiniteType f›, fun x hx => ?_⟩
  have hpx : fA (f x) = p := by
    change (f ≫ fA) x = p
    rwa [hbase]
  have hxj : f x ∈ Set.range j := by
    rw [hjrange]
    exact hpx
  obtain ⟨y', hy⟩ := hxj
  refine quasiFiniteAt_of_fiber_subset_range f i j g hcomm y' hy ?_
  intro z hz
  rw [hirange]
  change fB z = p
  rw [← hbase]
  exact (congrArg fA (show f z = f x from hz)).trans hpx

set_option backward.isDefEq.respectTransparency false in
/--
概要：ファイバー上の指定点を持ち上げる、アフィン空間の点付き étale 近傍上の有限な開閉部分。
方針：ファイバーの Noether 正規化から得た準有限性に、準有限代数の étale 局所有限化を適用する。
規約：多項式環の点の剰余体を保ち、有限部分の指定ファイバーは一点。
使われ方：相対 Noether 正規化の局所有限射の構成。
-/
theorem exists_etale_finite_piece_over_polynomial
    {R B : Type u} [CommRing R] [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
    (p : Spec (.of R))
    (x : Spec (.of B)) (hx : Spec.map (CommRingCat.ofHom (algebraMap R B)) x = p) :
    ∃ n : ℕ, ∃ b : Fin n → B,
      let A := MvPolynomial (Fin n) R
      let φ := MvPolynomial.aeval (R := R) b
      letI : Algebra A B := φ.toRingHom.toAlgebra
      let q := x.asIdeal.comap φ.toRingHom
      letI : q.IsPrime := inferInstance
      ∃ (T : Type u) (_ : CommRing T) (_ : Algebra A T) (_ : Algebra.Etale A T)
        (y : Ideal T) (_ : y.IsPrime) (_ : y.LiesOver q)
        (e : T ⊗[A] B) (_ : IsIdempotentElem e)
        (z : Ideal (T ⊗[A] B)) (_ : z.IsPrime) (_ : z.LiesOver y),
        z.comap Algebra.TensorProduct.includeRight.toRingHom = x.asIdeal ∧ e ∉ z ∧
        Function.Bijective (Ideal.ResidueField.mapₐ q y (Algebra.ofId _ _) (y.over_def q)) ∧
        Module.Finite T (Localization.Away e) ∧
        ∀ z' : Ideal (T ⊗[A] B), z'.IsPrime → z'.LiesOver y → e ∉ z' → z' = z := by
  have hnonempty : Nonempty (PrimeSpectrum (p.asIdeal.ResidueField ⊗[R] B)) := by
    obtain ⟨_, hrange⟩ := fiber_projection_spec R B p
    have hx' : x ∈ (Spec.map (CommRingCat.ofHom (algebraMap R B))) ⁻¹' {p} := hx
    obtain ⟨z, _⟩ := hrange.symm ▸ hx'
    exact ⟨z⟩
  let : Nontrivial (p.asIdeal.ResidueField ⊗[R] B) :=
    PrimeSpectrum.nonempty_iff_nontrivial.mp hnonempty
  obtain ⟨n, b, hft, hq⟩ := exists_polynomial_quasiFiniteAt_on_fiber (B := B) p
  let A := MvPolynomial (Fin n) R
  let φ : A →ₐ[R] B := MvPolynomial.aeval b
  let f := Spec.map (CommRingCat.ofHom φ.toRingHom)
  let : LocallyOfFiniteType f := hft
  let : Algebra A B := φ.toRingHom.toAlgebra
  let : Algebra.FiniteType A B := RingHom.finiteType_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hft)
  let q := x.asIdeal.comap φ.toRingHom
  let : q.IsPrime := inferInstance
  let : x.asIdeal.LiesOver q := ⟨rfl⟩
  have hqx : f.QuasiFiniteAt x := hq x hx
  have hopen : IsOpen {f.asFiber x} :=
    Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mp hqx
  rw [← (f.fiberHomeo (f x)).isOpen_image] at hopen
  have hdisc : IsOpen ({⟨x, rfl⟩} : Set (f ⁻¹' {f x})) := by
    simpa only [Set.image_singleton, Scheme.Hom.asFiber, Homeomorph.apply_symm_apply] using hopen
  let : Algebra.QuasiFiniteAt A x.asIdeal :=
    (Algebra.quasiFiniteAt_iff_isOpen_singleton_fiber (R := A) x).mpr hdisc
  exact ⟨n, b, Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq q x.asIdeal⟩

end SerrePositivity.AlgebraicGeometry
