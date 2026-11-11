module

public import SerrePositivity.AlgebraicGeometry.FiniteFreePolynomialMarker
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Unramified.LocalStructure

/-!
概要：アフィン空間への étale チャートで、指定点を含む平坦な準有限切断を作る。
方針：座標空間で有限自由な閉部分を作り、étale 写像に沿って引き戻す。
規約：指定点の座標は、基底の商環上で整と仮定する。
使われ方：滑らかな射の指定ファイバーを標識して、連結成分を基底近傍へ広げる。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.AlgebraicGeometry

open scoped TensorProduct

/--
概要：アフィン空間への étale チャートの点の座標が基底の商環上で整なら、
その点を含む閉部分で基底上平坦かつ準有限なものがある。
方針：有限自由な座標切断を底変換し、étale 性から平坦性と準有限性を得る。
規約：指定点を代数準同型で表し、閉部分は有限自由な座標切断のテンソル積で表す。
使われ方：Stacks 057J に必要な、滑らかなファイバーの標識の構成。
-/
theorem exists_flat_quasiFinite_etale_polynomial_marker
    {R : Type u} {K B F : Type*} [CommRing R] [CommRing K] [CommRing B] [CommRing F]
    [Algebra R K] [Algebra R B] [Algebra R F] [Algebra K F] [IsScalarTower R K F]
    (hRK : Function.Surjective (algebraMap R K)) {n : ℕ}
    [Algebra (MvPolynomial (Fin n) R) B] [IsScalarTower R (MvPolynomial (Fin n) R) B]
    [Algebra.Etale (MvPolynomial (Fin n) R) B] (y : B →ₐ[R] F)
    (hy : ∀ i : Fin n,
      IsIntegral K (y (algebraMap (MvPolynomial (Fin n) R) B (MvPolynomial.X i)))) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra R C) (_ : Module.Finite R C)
      (_ : Module.Free R C) (φ : MvPolynomial (Fin n) R →ₐ[R] C),
      Function.Surjective φ ∧
      let A := MvPolynomial (Fin n) R
      letI : Algebra A C := φ.toRingHom.toAlgebra
      letI : IsScalarTower R A C := IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
      let D := C ⊗[A] B
      Algebra.FiniteType R D ∧ Module.Flat R D ∧ Algebra.QuasiFinite R D ∧
        ∃ z : D →ₐ[R] F, z.comp (Algebra.TensorProduct.includeRight.restrictScalars R) = y := by
  let A := MvPolynomial (Fin n) R
  let x (i : Fin n) := y (algebraMap A B (MvPolynomial.X i))
  obtain ⟨C, _, _, _, _, φ, ψ, hφ, hψ⟩ :=
    exists_finiteFree_quotient_of_integral_coordinates_over_quotient hRK x hy
  let : Algebra A C := φ.toRingHom.toAlgebra
  let : IsScalarTower R A C := IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  let D := C ⊗[A] B
  let : Algebra.FiniteType R D := .trans (inferInstance : Algebra.FiniteType R C)
    (inferInstance : Algebra.FiniteType C D)
  let : Module.Flat R D := Module.Flat.trans R C D
  let : Algebra.QuasiFinite R D := Algebra.QuasiFinite.trans R C D
  let : Algebra C F := ψ.toRingHom.toAlgebra
  let : IsScalarTower R C F := IsScalarTower.of_algebraMap_eq' ψ.comp_algebraMap.symm
  let : Algebra A F := (ψ.comp φ).toRingHom.toAlgebra
  let : IsScalarTower A C F := IsScalarTower.of_algebraMap_eq' rfl
  have hy' : y.comp (IsScalarTower.toAlgHom R A B) = ψ.comp φ := by
    rw [hψ]
    exact MvPolynomial.algHom_ext fun i => (MvPolynomial.aeval_X x i).symm
  let y' : B →ₐ[A] F :=
    ⟨y.toRingHom, fun a => DFunLike.congr_fun hy' a⟩
  let z : D →ₐ[C] F := Algebra.TensorProduct.lift (Algebra.ofId C F) y' fun _ _ => .all _ _
  refine ⟨C, _, _, inferInstance, inferInstance, φ, hφ, inferInstance, inferInstance, inferInstance,
    z.restrictScalars R, ?_⟩
  ext b
  change z (1 ⊗ₜ[A] b) = y' b
  simpa only [map_one, one_mul] using
    Algebra.TensorProduct.lift_tmul (Algebra.ofId C F) y' (fun _ _ => .all _ _) (1 : C) b

end SerrePositivity.AlgebraicGeometry
