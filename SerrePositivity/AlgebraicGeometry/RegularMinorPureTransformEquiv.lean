module

public import SerrePositivity.AlgebraicGeometry.RegularMinorGraphKernel
public import SerrePositivity.AlgebraicGeometry.PureTransformPivotEquiv
public import SerrePositivity.AlgebraicGeometry.PureTransformBoundaryComparison
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
概要：KST §5、Stacks 0810・080Z の正則ピボットからの純変換の実同型。
方針：随伴行列の擬関係式を正規化し、高次小行列式の消滅から核を消去する。
規約：純変換は元の加群の境界ねじれによる商として保持する。
使われ方：係数 blowup のチャート上での純変換の局所自由性。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped Matrix

set_option backward.isDefEq.respectTransparency false in
/--
概要：正則ピボットと正規化した随伴関係式から純変換と補成分の実線形同型を得る。
方針：実際の表示から核の包含を導き、境界の冪ねじれと正則性によって生成元を消去する。
規約：KST §5、Stacks 0810, Lemma 38.30.2・080Z, Lemma 15.8.9、二つの境界元を区別する。
使われ方：正則単項の小行列式と次次数の消滅による純変換の自由性判定。
-/
def regularMinorBoundaryPresentationComplementEquiv
    {R M m n : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Finite m] {k : ℕ}
    (H : Matrix m n R) (r : Fin k → m) (hr : Function.Injective r) (c : Fin k → n)
    (q : (m → R) →ₗ[R] M) (hq : Function.Surjective q)
    (hH : Submodule.span R (Set.range H.col) = LinearMap.ker q)
    (d f : R) (hd : IsRegular d) (hf : IsRegular f) (N : ℕ) (hdf : d ∣ f ^ N)
    (u : Rˣ) (hdet : (H.submatrix r c).det = d * (u : R))
    (C : Matrix {i : m // i ∉ Set.range r} (Fin k) R)
    (hBC : (H.submatrix Subtype.val c) * (H.submatrix r c).adjugate = d • C)
    (hzero : matrixMinorIdeal H (k + 1) = ⊥) :
    ({i : m // i ∉ Set.range r} → R) ≃ₗ[R] modulePureTransform f M := by
  classical
  let : Fintype m := Fintype.ofFinite m
  let K := {i : m // i ∉ Set.range r}
  let E := rowPartitionLinearEquiv r hr R
  let q' := q.comp E.symm.toLinearMap
  let A := H.submatrix r c
  let B := H.submatrix (Subtype.val : K → m) c
  let D := H.submatrix id c
  let t : (Fin k → R) →ₗ[R] ((Fin k → R) × (K → R)) :=
    ((u : R) • LinearMap.id).prod C.mulVecLin
  have hprod : E.toLinearMap.comp D.mulVecLin = A.mulVecLin.prod B.mulVecLin :=
    rowPartitionLinearEquiv_comp_mulVecLin r hr R D
  have hD : LinearMap.range D.mulVecLin ≤ LinearMap.ker q := by
    rw [Matrix.range_mulVecLin, ← hH]
    apply Submodule.span_mono
    rintro z ⟨j, rfl⟩
    exact ⟨c j, rfl⟩
  have hrel : q'.comp (A.mulVecLin.prod B.mulVecLin) = 0 := by
    rw [← hprod]
    apply LinearMap.ext
    intro x
    change q (E.symm (E (D.mulVecLin x))) = 0
    rw [E.symm_apply_apply]
    exact hD ⟨x, rfl⟩
  have hdA : IsRegular A.det := by
    rw [hdet]
    exact hd.mul u.isRegular
  have hCA : C * A = (u : R) • B := normalizedAdjugate_mul_pivot A B C d hd u hdet hBC
  have hker : LinearMap.ker q' ≤ LinearMap.range t :=
    kernel_le_regularMinorGraph H r hr c hdA hzero q hH u C hCA
  have ht : ∀ x, q' (t x) ∈ boundaryTorsion f M := by
    intro x
    apply boundaryTorsion_le_of_dvd_pow d f M N hdf
    apply (mem_boundaryTorsion_iff d M _).mpr
    refine ⟨1, ?_⟩
    have hs : d • t x = (A.mulVecLin.prod B.mulVecLin) (A.adjugate *ᵥ x) := by
      apply Prod.ext
      · change d • ((u : R) • x) = A *ᵥ (A.adjugate *ᵥ x)
        rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, hdet,
          Matrix.smul_mulVec, Matrix.one_mulVec, mul_smul]
      · change d • (C *ᵥ x) = B *ᵥ (A.adjugate *ᵥ x)
        rw [Matrix.mulVec_mulVec, hBC, Matrix.smul_mulVec]
    rw [pow_one, ← map_smul, hs]
    exact LinearMap.congr_fun hrel _
  have hfK : IsSMulRegular (K → R) f := Module.Flat.isSMulRegular_of_isRegular hf
  exact pureTransformPivotComplementEquiv f q' t (LinearEquiv.smulOfUnit u) hfK
    (hq.comp E.symm.surjective) ht hker rfl

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
