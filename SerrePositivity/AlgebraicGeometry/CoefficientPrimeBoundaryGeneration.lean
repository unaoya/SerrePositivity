module

public import SerrePositivity.AlgebraicGeometry.CoefficientIdealPrimeLocalization
public import SerrePositivity.AlgebraicGeometry.SplitAlgebraCoefficientBaseChange
public import SerrePositivity.AlgebraicGeometry.FiniteFreePresentationBaseChange
public import SerrePositivity.AlgebraicGeometry.AdjugateBoundaryGeneration

/-!
概要：KST §5、Stacks 0810, Lemma 38.30.2 の係数中心の特別な局所環での境界純変換の生成。
方針：係数の正則単項化を拡大素点へ移し、基底変更した完全な表示に生成元除去を適用する。
規約：元の境界と小行列式の共通因子は区別する。
使われ方：一般有限型加群の平坦化で、純変換の局所生成元数を評価する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

/--
概要：係数イデアルが正則単項となり共通因子が境界冪を割るとき、拡大素点の局所環で境界純変換の生成元を削減する。
方針：拡大素点での正則単項化と表示の任意の基底変更を、異なる境界元の比較全射に接続する。
規約：KST §5、Stacks 0810, Lemma 38.30.2、生成元数は元の表示の行数から小行列式の次数を引く。
使われ方：実際の係数 blowup チャートの局所環で純変換への有限自由全射を得る。
-/
theorem coefficient_prime_boundary_generator_bound
    {A B C M ι m n : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [AddCommGroup M] [Module B M] [Fintype m] [Finite n]
    (e : B →ₗ[A] (ι →₀ A)) (p : (ι →₀ A) →ₗ[A] B) (hpe : p.comp e = LinearMap.id)
    (H : Matrix m n B) (k : ℕ) (q : (m → B) →ₗ[B] M) (hq : Function.Surjective q)
    (hH : Submodule.span B (Set.range H.col) = LinearMap.ker q)
    (c f : C) (hc : IsRegular c) (N : ℕ) (hcf : c ∣ f ^ N)
    (hcoeff : (splitAlgebraCoefficientIdeal e (matrixMinorIdeal H k)).map (algebraMap A C) =
      Ideal.span {c}) (P : Ideal C) (hP : P ≠ ⊤) [(P.map (algebraMap C (C ⊗[A] B))).IsPrime] :
    let D := C ⊗[A] B
    let L := Localization.AtPrime (P.map (algebraMap C D))
    let φ : B →+* L := (algebraMap D L).comp
      (Algebra.TensorProduct.includeRight : B →ₐ[A] D).toRingHom
    letI : Algebra B L := φ.toAlgebra
    ∃ g : (Fin (Fintype.card m - k) → L) →ₗ[L]
        modulePureTransform (algebraMap D L (algebraMap C D f)) (L ⊗[B] M),
      Function.Surjective g := by
  classical
  let D := C ⊗[A] B
  let L := Localization.AtPrime (P.map (algebraMap C D))
  let ψ := algebraMap D L
  let φB : B →+* D := (Algebra.TensorProduct.includeRight : B →ₐ[A] D).toRingHom
  let φ : B →+* L := ψ.comp φB
  let : Algebra B L := φ.toAlgebra
  let e' := splitAlgebraTensorEmbedding (C := C) e
  let p' := splitAlgebraTensorRetraction (C := C) p
  have hs : p'.comp e' = LinearMap.id := splitAlgebraTensorRetraction_comp_embedding e p hpe
  have hcoeff' : splitAlgebraCoefficientIdeal e' ((matrixMinorIdeal H k).map φB) = Ideal.span {c} :=
    (splitAlgebraCoefficientIdeal_baseChange e p hpe _).trans hcoeff
  have hloc := coefficientIdeal_regular_principal_at_extended_prime e' p' hs c
    ((matrixMinorIdeal H k).map φB) hc hcoeff' P hP
  let cL := ψ (algebraMap C D c)
  let fL := ψ (algebraMap C D f)
  have hcL : IsRegular cL := isRegular_iff_mem_nonZeroDivisors.mpr hloc.1
  have hcfL : cL ∣ fL ^ N := by
    simpa only [RingHom.comp_apply, map_pow] using map_dvd (ψ.comp (algebraMap C D)) hcf
  have hminor : matrixMinorIdeal (H.map (algebraMap B L)) k = Ideal.span {cL} := by
    rw [← matrixMinorIdeal_map H k (algebraMap B L)]
    change (matrixMinorIdeal H k).map (ψ.comp φB) = Ideal.span {cL}
    rw [← Ideal.map_map]
    exact hloc.2
  let qL := finiteFreePresentationBaseChange (C := L) q
  have hqL : Function.Surjective qL := finiteFreePresentationBaseChange_surjective q hq
  have hker := finiteFreePresentationBaseChange_columnSpan_eq_ker (C := L) H q hq hH
  have hrel : ∀ j, qL ((H.map (algebraMap B L)).col j) = 0 := by
    intro j
    exact hker.le (Submodule.subset_span ⟨j, rfl⟩)
  exact exists_fin_surjection_boundaryPureTransform_of_regular_minorIdeal
    (H.map (algebraMap B L)) k cL fL hcL N hcfL qL hqL hrel hminor

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
