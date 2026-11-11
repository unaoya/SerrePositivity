module

public import SerrePositivity.AlgebraicGeometry.EtaleResidueFieldMarker
public import SerrePositivity.AlgebraicGeometry.FiberConnectedComponentPrincipalOpen
public import SerrePositivity.AlgebraicGeometry.PurelyTranscendentalFiberConnected
public import SerrePositivity.AlgebraicGeometry.RationalFiberPointSpecialization
public import SerrePositivity.AlgebraicGeometry.SmoothFiniteMarkerIntegralOpen

/-!
概要：連結な指定ファイバーが純超越な点を持つ étale チャートを、幾何学的整な開部分に広げる。
方針：純超越な点から有限分離点を選び、初等 étale 近傍上の有限平坦な標識を使う。
規約：指定ファイバーは連結とし、始域はアフィン空間上の étale チャートとする。
使われ方：相対 Noether 正規化で切り出した滑らかなファイバー成分を広げる。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory
open scoped TensorProduct

/--
概要：指定点の剰余体の同型から、ファイバー上の体値点を取り出せる。
方針：元の代数から剰余体へ写し、その同型を合成してファイバーへ延長する。
規約：得られる体値点の元の代数への縮約は指定点に等しい。
使われ方：相対 Noether 正規化の純超越な剰余体を持つ点から、指定成分を選ぶ。
-/
theorem exists_fiber_evaluation_of_residueField_equiv
    {R B F : Type u} [CommRing R] [CommRing B] [Field F] [Algebra R B] [Algebra R F]
    (p : Ideal R) [p.IsPrime] [Algebra p.ResidueField F] [IsScalarTower R p.ResidueField F]
    (q : Ideal B) [q.IsPrime] [q.LiesOver p] (e : q.ResidueField ≃ₐ[R] F) :
    ∃ y : p.Fiber B →ₐ[p.ResidueField] F,
      RingHom.ker (y.toRingHom.comp
        (Algebra.TensorProduct.includeRight : B →ₐ[R] p.Fiber B).toRingHom) = q := by
  let k := p.ResidueField
  let f := e.toAlgHom.comp (IsScalarTower.toAlgHom R B q.ResidueField)
  let y : p.Fiber B →ₐ[k] F :=
    Algebra.TensorProduct.lift (Algebra.ofId k F) f fun _ _ => .all _ _
  refine ⟨y, ?_⟩
  have h : y.toRingHom.comp
      (Algebra.TensorProduct.includeRight : B →ₐ[R] p.Fiber B).toRingHom = f.toRingHom := by
    apply RingHom.ext
    intro b
    change y ((1 : k) ⊗ₜ[R] b) = f b
    simpa only [map_one, one_mul] using
      Algebra.TensorProduct.lift_tmul (Algebra.ofId k F) f (fun _ _ => .all _ _) (1 : k) b
  rw [h]
  change RingHom.ker (e.toRingHom.comp (algebraMap B q.ResidueField)) = q
  rw [RingHom.ker_comp_of_injective _ e.injective, Ideal.ker_algebraMap_residueField]

/--
概要：連結な指定ファイバーが有理関数体に値を取る点を持てば、基底の初等 étale 近傍上で
そのファイバーを含む幾何学的整な準コンパクト開が存在する。
方針：純超越な点で幾何学的連結性を示し、その特殊化から作った有限標識で開部分を降下する。
規約：始域は多項式代数上 étale とし、基底は Noether 環とする。
使われ方：Stacks 057J の相対 Noether 正規化先における連結ファイバーの場合。
-/
theorem exists_etale_geometricallyIntegral_open_of_connected_rational_fiber
    {R B ι : Type u} [CommRing R] [IsNoetherianRing R] [CommRing B]
    [Algebra R B] [Finite ι] {n : ℕ}
    [Algebra (MvPolynomial (Fin n) R) B] [IsScalarTower R (MvPolynomial (Fin n) R) B]
    [Algebra.Etale (MvPolynomial (Fin n) R) B] (p : PrimeSpectrum R)
    [ConnectedSpace (PrimeSpectrum (p.asIdeal.ResidueField ⊗[R] B))]
    (y : p.asIdeal.ResidueField ⊗[R] B →ₐ[p.asIdeal.ResidueField]
      FractionRing (MvPolynomial ι p.asIdeal.ResidueField)) :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T) (_ : Algebra.Etale R T)
      (s : PrimeSpectrum T) (_ : s.asIdeal.LiesOver p.asIdeal),
      Function.Bijective
        (Ideal.ResidueField.mapₐ p.asIdeal s.asIdeal (Algebra.ofId R T)
          (s.asIdeal.over_def p.asIdeal)) ∧
      let E := T ⊗[R] B
      let f := Spec.map (CommRingCat.ofHom (algebraMap T E))
      ∃ (U : (Spec (.of T)).Opens) (V : (Spec (.of E)).Opens), IsAffineOpen U ∧ s ∈ U ∧
        IsCompact (V : Set (Spec (.of E))) ∧ f ⁻¹' ({s} : Set (Spec (.of T))) ⊆ V ∧
        ∃ hVU : V ≤ f ⁻¹ᵁ U, GeometricallyIntegral ((Spec (.of E)).homOfLE hVU ≫ f ∣_ U) := by
  let k := p.asIdeal.ResidueField
  let P := MvPolynomial (Fin n) R
  let : Algebra.Smooth R B := Algebra.Smooth.comp R P B
  obtain ⟨F, _, _, hFinite, _, ⟨yF⟩⟩ :=
    exists_algHom_finite_separable_of_fractionRing_mvPolynomial y
  let : Module.Finite k F := hFinite
  let : Algebra R F := ((algebraMap k F).comp (algebraMap R k)).toAlgebra
  let : IsScalarTower R k F := IsScalarTower.of_algebraMap_eq' rfl
  let z : B →ₐ[R] F :=
    (yF.restrictScalars R).comp Algebra.TensorProduct.includeRight
  obtain ⟨T, _, _, _, s, hs, _, hκ, M, _, _, _, _, ⟨σ⟩, m, hm⟩ :=
    exists_etale_finiteProjective_marker_of_integral_residueField (n := n) p.asIdeal z
      (fun _ => IsIntegral.of_finite (R := k) _)
  let s' : PrimeSpectrum T := ⟨s, hs⟩
  refine ⟨T, _, _, inferInstance, s', inferInstance, hκ, ?_⟩
  let E := T ⊗[R] B
  let : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing R T
  have hConn (L : Type u) [Field L] [Algebra T L]
      (hL : (⊥ : PrimeSpectrum L).comap (algebraMap T L) = s') :
      ConnectedSpace (PrimeSpectrum (L ⊗[T] E)) := by
    let : Algebra R L := ((algebraMap T L).comp (algebraMap R T)).toAlgebra
    let : IsScalarTower R T L := IsScalarTower.of_algebraMap_eq' rfl
    have hp : (⊥ : PrimeSpectrum L).comap (algebraMap R L) = p := by
      rw [IsScalarTower.algebraMap_eq R T L, PrimeSpectrum.comap_comp_apply, hL]
      exact PrimeSpectrum.ext (s.over_def p.asIdeal).symm
    let : ConnectedSpace (PrimeSpectrum (L ⊗[R] B)) :=
      connectedSpace_tensor_of_rational_point_in_fiber p y L hp
    let e := Algebra.TensorProduct.cancelBaseChange R T L L B
    exact (PrimeSpectrum.homeomorphOfRingEquiv e.toRingEquiv).connectedSpace_iff.mpr inferInstance
  exact exists_geometricallyIntegral_open_of_smooth_finite_flat_marker σ s' hConn
    ⟨m, PrimeSpectrum.ext hm⟩

/--
概要：純超越な点を通る指定ファイバーの連結成分は、基底の初等 étale 近傍上で
幾何学的整な準コンパクト開に広がる。
方針：指定点を残す主開で連結成分を取り出し、そのチャートに有限平坦な標識を作る。
規約：始域は多項式代数上 étale とし、最初の主開も結論に含める。
使われ方：Stacks 057J から相対 Noether 正規化先の局所構成へ進む。
-/
theorem exists_etale_geometricallyIntegral_open_of_rational_fiber_point
    {R B ι : Type u} [CommRing R] [IsNoetherianRing R] [CommRing B]
    [Algebra R B] [Finite ι] {n : ℕ}
    [Algebra (MvPolynomial (Fin n) R) B] [IsScalarTower R (MvPolynomial (Fin n) R) B]
    [Algebra.Etale (MvPolynomial (Fin n) R) B] (p : PrimeSpectrum R)
    (y : p.asIdeal.ResidueField ⊗[R] B →ₐ[p.asIdeal.ResidueField]
      FractionRing (MvPolynomial ι p.asIdeal.ResidueField)) :
    ∃ b : B, y (1 ⊗ₜ[R] b) ≠ 0 ∧
      ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T) (_ : Algebra.Etale R T)
        (s : PrimeSpectrum T) (_ : s.asIdeal.LiesOver p.asIdeal),
        Function.Bijective
          (Ideal.ResidueField.mapₐ p.asIdeal s.asIdeal (Algebra.ofId R T)
            (s.asIdeal.over_def p.asIdeal)) ∧
        let E := T ⊗[R] Localization.Away b
        let f := Spec.map (CommRingCat.ofHom (algebraMap T E))
        ∃ (U : (Spec (.of T)).Opens) (V : (Spec (.of E)).Opens), IsAffineOpen U ∧ s ∈ U ∧
          IsCompact (V : Set (Spec (.of E))) ∧ f ⁻¹' ({s} : Set (Spec (.of T))) ⊆ V ∧
          ∃ hVU : V ≤ f ⁻¹ᵁ U, GeometricallyIntegral ((Spec (.of E)).homOfLE hVU ≫ f ∣_ U) := by
  let P := MvPolynomial (Fin n) R
  let : Algebra.FiniteType R B := .trans (inferInstance : Algebra.FiniteType R P)
    (inferInstance : Algebra.FiniteType P B)
  obtain ⟨b, hb, hConn, _, z, _⟩ := exists_away_connected_fiber_of_point p.asIdeal y
  let L := Localization.Away b
  let : IsScalarTower R P L := .to₁₂₄ R P B L
  let : Algebra.Etale P L := inferInstanceAs (Algebra.Etale P (Localization.Away b))
  exact ⟨b, hb, exists_etale_geometricallyIntegral_open_of_connected_rational_fiber (n := n) p z⟩

end SerrePositivity.AlgebraicGeometry
