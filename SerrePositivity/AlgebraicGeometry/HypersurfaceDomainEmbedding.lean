module

public import SerrePositivity.AlgebraicGeometry.GenericFreeAlgebra
import Mathlib.Algebra.Ring.Hom.InjSurj
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
概要：体拡大後に整な代数へ埋め込まれる超曲面の方程式は、体拡大後も既約。
方針：体拡大で単射を保ち、係数変更後の多項式商が整域であることを示す。
規約：方程式は非零とし、埋め込みは元の体上で与える。
使われ方：滑らかな生成ファイバーの標準 étale チャートから作る超曲面方程式の絶対既約性。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open scoped TensorProduct

/--
概要：超曲面環が体拡大後に整域になる代数へ埋め込まれれば、方程式はその体上で既約。
方針：テンソル積で保たれる単射と、主イデアルの素性の判定を使う。
規約：方程式は非零とする。
使われ方：標準 étale チャートの最小多項式による模型。
-/
theorem irreducible_map_of_hypersurface_injective
    {k F B σ : Type*} [Field k] [Field F] [Algebra k F]
    [CommRing B] [Algebra k B] [IsDomain (F ⊗[k] B)]
    (P : MvPolynomial σ k) (hP : P ≠ 0)
    (j : (MvPolynomial σ k ⧸ Ideal.span {P}) →ₐ[k] B) (hj : Function.Injective j) :
    Irreducible (MvPolynomial.map (algebraMap k F) P) := by
  let I := Ideal.span ({P} : Set (MvPolynomial σ k))
  let f := MvPolynomial.map (σ := σ) (algebraMap k F)
  let J := I.map f
  let : Module.Free k F := Module.Free.of_divisionRing k F
  let jF := Algebra.TensorProduct.map (AlgHom.id k F) j
  have hjF : Function.Injective jF :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := F) j.toLinearMap hj
  let : IsDomain (F ⊗[k] (MvPolynomial σ k ⧸ I)) :=
    Function.Injective.isDomain jF.toRingHom hjF
  let e := mvPolynomialQuotientTensorEquiv (C := F) I
  let : IsDomain (MvPolynomial σ F ⧸ J) := e.symm.toRingEquiv.isDomain
  have hJ : J.IsPrime := (Ideal.Quotient.isDomain_iff_prime J).mp inferInstance
  have hEq : J = Ideal.span {f P} := by
    change (Ideal.span {P}).map f = _
    rw [Ideal.map_span, Set.image_singleton]
  have hNonzero : f P ≠ 0 :=
    by simpa only [map_zero, f] using
      (MvPolynomial.map_injective _ (algebraMap k F).injective).ne hP
  rw [hEq] at hJ
  exact ((Ideal.span_singleton_prime hNonzero).mp hJ).irreducible

end SerrePositivity.AlgebraicGeometry
