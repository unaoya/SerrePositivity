module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
概要：各座標が整であるアフィン空間の点を含む有限自由な閉部分を構成する。
方針：各座標を満たすモニック多項式を選び、根添加を繰り返す。
規約：座標の値は任意の基底代数に取れる。
使われ方：滑らかなファイバーの成分を追うための有限局所自由な標識。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.AlgebraicGeometry

open Polynomial

/--
概要：各座標の値が基底上整なら、アフィン空間への点は基底上有限自由な閉部分を経由する。
方針：座標を一つずつ加え、各段階でモニック多項式の根添加を使う。
規約：閉部分は多変数多項式環からの全射で表す。
使われ方：有限型のファイバーの閉点を通る有限自由な標識を取る。
-/
theorem exists_finiteFree_quotient_of_integral_coordinates
    {R : Type u} {T : Type*} [CommRing R] [CommRing T] [Algebra R T]
    {n : ℕ} (x : Fin n → T) (hx : ∀ i, IsIntegral R (x i)) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra R C) (_ : Module.Finite R C)
      (_ : Module.Free R C) (φ : MvPolynomial (Fin n) R →ₐ[R] C) (ψ : C →ₐ[R] T),
      Function.Surjective φ ∧ ψ.comp φ = MvPolynomial.aeval x := by
  induction n with
  | zero =>
    let e := MvPolynomial.isEmptyAlgEquiv R (Fin 0)
    refine ⟨R, _, _, inferInstance, inferInstance, e.toAlgHom, Algebra.ofId R T,
      e.surjective, ?_⟩
    exact MvPolynomial.algHom_ext (fun i => i.elim0)
  | succ n ih =>
    obtain ⟨C, _, _, _, _, φ, ψ, hφ, hψ⟩ := ih (fun i => x i.succ) (fun i => hx i.succ)
    obtain ⟨f, hf, hfx⟩ := hx 0
    let p := f.map (algebraMap R C)
    let D := AdjoinRoot p
    let : Module.Free C D := (hf.map _).free_adjoinRoot
    let : Module.Finite C D := (hf.map _).finite_adjoinRoot
    let : Module.Free R D := Module.Free.trans (S := C)
    let : Module.Finite R D := Module.Finite.trans C D
    let q := ((AdjoinRoot.mkₐ p).restrictScalars R).comp (Polynomial.mapAlgHom φ)
    let j := q.comp (MvPolynomial.finSuccEquiv R n).toAlgHom
    have hp : p.eval₂ ψ.toRingHom (x 0) = 0 := by
      have hψR : ψ.toRingHom.comp (algebraMap R C) = algebraMap R T :=
        RingHom.ext ψ.commutes
      rwa [Polynomial.eval₂_map, hψR]
    let k := AdjoinRoot.liftAlgHom p ψ (x 0) hp
    refine ⟨D, _, _, inferInstance, inferInstance, j, k,
      AdjoinRoot.mk_surjective.comp
        ((Polynomial.map_surjective φ.toRingHom hφ).comp
          (MvPolynomial.finSuccEquiv R n).surjective),
      ?_⟩
    apply MvPolynomial.algHom_ext
    intro i
    refine Fin.cases ?_ (fun t => ?_) i
    · have hj : j (MvPolynomial.X 0) = AdjoinRoot.root p := by
        simp [j, q, MvPolynomial.finSuccEquiv_X_zero, AdjoinRoot.mk_X]
      change k (j (MvPolynomial.X 0)) = MvPolynomial.aeval x (MvPolynomial.X 0)
      rw [hj, MvPolynomial.aeval_X]
      exact AdjoinRoot.liftAlgHom_root p ψ (x 0) hp
    · have hj : j (MvPolynomial.X t.succ) = AdjoinRoot.of p (φ (MvPolynomial.X t)) := by
        simp [j, q, MvPolynomial.finSuccEquiv_X_succ, AdjoinRoot.mk_C]
      change k (j (MvPolynomial.X t.succ)) = MvPolynomial.aeval x (MvPolynomial.X t.succ)
      rw [hj, MvPolynomial.aeval_X]
      exact (AdjoinRoot.liftAlgHom_of p ψ (x 0) hp _).trans
        (by simpa using DFunLike.congr_fun hψ (MvPolynomial.X t))

/--
概要：基底の商環上で整な座標を持つ点は、元の基底上の有限自由な閉部分を経由する。
方針：各座標が満たすモニック多項式の係数を持ち上げる。
規約：基底から商環への写像の全射性を仮定する。
使われ方：基底の局所環から剰余体へ移したアフィン空間の閉点を標識する。
-/
theorem exists_finiteFree_quotient_of_integral_coordinates_over_quotient
    {R : Type u} {K T : Type*} [CommRing R] [CommRing K] [CommRing T]
    [Algebra R K] [Algebra R T] [Algebra K T] [IsScalarTower R K T]
    (hRK : Function.Surjective (algebraMap R K)) {n : ℕ}
    (x : Fin n → T) (hx : ∀ i, IsIntegral K (x i)) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra R C) (_ : Module.Finite R C)
      (_ : Module.Free R C) (φ : MvPolynomial (Fin n) R →ₐ[R] C) (ψ : C →ₐ[R] T),
      Function.Surjective φ ∧ ψ.comp φ = MvPolynomial.aeval x := by
  apply exists_finiteFree_quotient_of_integral_coordinates x
  intro i
  obtain ⟨p, hp, hpx⟩ := hx i
  have hlift : p ∈ Polynomial.lifts (algebraMap R K) :=
    Polynomial.map_surjective _ hRK p
  obtain ⟨f, hf, _, hfm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hp
  refine ⟨f, hfm, ?_⟩
  change f.eval₂ (algebraMap R T) (x i) = 0
  rw [IsScalarTower.algebraMap_eq R K T, ← Polynomial.eval₂_map, hf]
  exact hpx

end SerrePositivity.AlgebraicGeometry
