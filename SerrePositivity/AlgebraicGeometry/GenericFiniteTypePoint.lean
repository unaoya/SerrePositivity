module

public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Jacobson.Ring

/-!
概要：有限型アフィンの幾何学的生成ファイバーが空なら、台の稠密主開上で空になる。
方針：分数体への底変換の極大イデアルから幾何学的な点を作り、空の場合は分母を払う。
規約：台は整域とし、幾何学的生成点の体には分数体の代数閉包を使う。
使われ方：多項式の非自明な因数分解を表す有限型代数を稠密開上で消す。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open scoped TensorProduct nonZeroDivisors

/--
概要：整域上の有限型代数が幾何学的生成点を持たなければ、基底のある非零元が代数で零になる。
方針：生成ファイバーが非零なら、極大イデアルの剰余体を分数体の代数閉包へ埋め込む。
規約：幾何学的生成点を基底上の代数準同型で表す。
使われ方：有限型な因数分解の方程式が稠密主開上で解を持たないことを示す。
-/
theorem exists_nonzero_algebraMap_eq_zero_of_isEmpty_algHom_algebraicClosure
    {A B K : Type*} [CommRing A] [IsDomain A] [CommRing B] [Algebra A B]
    [Algebra.FiniteType A B] [Field K] [Algebra A K] [IsFractionRing A K]
    (h : IsEmpty (B →ₐ[A] AlgebraicClosure K)) :
    ∃ a : A, a ≠ 0 ∧ algebraMap A B a = 0 := by
  let D := K ⊗[A] B
  let : Algebra B D := Algebra.TensorProduct.rightAlgebra
  have hD : (1 : D) = 0 := by
    by_contra hn
    let : Nontrivial D := nontrivial_of_ne 1 0 hn
    obtain ⟨m, hm⟩ := Ideal.exists_maximal (α := D)
    let : Field (D ⧸ m) := Ideal.Quotient.field m
    let q : D →ₐ[K] D ⧸ m := Ideal.Quotient.mkₐ K m
    obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
      (inferInstance : Algebra.FiniteType K D)
    let g := q.comp f
    have hg : Function.Surjective g := Ideal.Quotient.mk_surjective.comp hf
    let : Algebra.IsAlgebraic K (D ⧸ m) := by
      rw [Algebra.isAlgebraic_iff_isIntegral, ← algebraMap_isIntegral_iff]
      have he : g.toRingHom.comp MvPolynomial.C = algebraMap K (D ⧸ m) := by
        ext x
        exact g.commutes x
      rw [← he]
      exact MvPolynomial.comp_C_integral_of_surjective_of_isJacobsonRing g.toRingHom hg
    let k : (D ⧸ m) →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
    exact h.false (((k.comp q).restrictScalars A).comp Algebra.TensorProduct.includeRight)
  let M := Algebra.algebraMapSubmonoid B A⁰
  have hz : algebraMap B D (1 : B) = algebraMap B D 0 := by simpa only [map_one, map_zero] using hD
  obtain ⟨⟨b, hb⟩, he⟩ := (IsLocalization.eq_iff_exists M D).mp hz
  obtain ⟨a, ha, rfl⟩ := hb
  exact ⟨a, mem_nonZeroDivisors_iff_ne_zero.mp ha, by simpa only [mul_one, mul_zero] using he⟩

end SerrePositivity.AlgebraicGeometry
