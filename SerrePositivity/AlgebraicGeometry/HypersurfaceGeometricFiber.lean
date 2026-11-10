module

public import SerrePositivity.AlgebraicGeometry.AbsoluteIrreducibilitySpecialization
public import SerrePositivity.AlgebraicGeometry.GenericFreeAlgebra
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
概要：幾何学的生成ファイバーの定義多項式が既約な超曲面は、稠密主開上で幾何学的整なファイバーを持つ。
方針：多項式商の底変換を係数変更として表し、特殊化した既約多項式の素性を使う。
規約：ファイバーは指定した基底の元を零にしない任意の体へのテンソル積で表す。
使われ方：アフィン射の幾何学的既約性を超曲面模型を通じて広げる。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open MvPolynomial
open scoped TensorProduct

/--
概要：分数体の代数閉包で既約な方程式を持つ超曲面は、基底のある主開上の任意の体で整域を与える。
方針：絶対既約性の特殊化と、多項式商の底変換の同型を合成する。
規約：基底は整域、方程式の変数は有限個とする。
使われ方：Stacks 0559 の超曲面模型。
-/
theorem exists_nonzero_forall_isDomain_tensor_hypersurface
    {A K σ : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
    [Finite σ] (P : MvPolynomial σ A)
    (hP : Irreducible (map (algebraMap A (AlgebraicClosure K)) P)) :
    ∃ a : A, a ≠ 0 ∧ ∀ (F : Type*) [Field F] [Algebra A F], algebraMap A F a ≠ 0 →
      IsDomain (F ⊗[A] (MvPolynomial σ A ⧸ Ideal.span {P})) := by
  obtain ⟨a, ha, h⟩ := exists_nonzero_forall_irreducible_map_of_generic P hP
  refine ⟨a, ha, ?_⟩
  intro F _ _ haF
  let j := map (σ := σ) (algebraMap A F)
  have hPrime : Prime (j P) := (h F (algebraMap A F) haF).prime
  have : ((Ideal.span {P}).map j).IsPrime := by
    rw [Ideal.map_span, Set.image_singleton]
    exact Ideal.isPrime_span_singleton_of_prime hPrime
  exact (mvPolynomialQuotientTensorEquiv (C := F) (Ideal.span {P})).toRingEquiv.isDomain

end SerrePositivity.AlgebraicGeometry
