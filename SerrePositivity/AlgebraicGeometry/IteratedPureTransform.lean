module

public import SerrePositivity.AlgebraicGeometry.BoundaryPowerLift
public import SerrePositivity.AlgebraicGeometry.PureTransformImage
public import SerrePositivity.AlgebraicGeometry.PureTransformPullbacks
public import SerrePositivity.AlgebraicGeometry.ScalarInverseBaseChange
public import SerrePositivity.AlgebraicGeometry.TensorPureTransformBaseChange

/-!
概要：二段の係数変更で最初に純変換を取っても、最後の純変換は同じ。
方針：最初の商写像の基底変換の核は境界冪で消え、最後の純変換で消えることを使う。
規約：最初の加群の境界ねじれを一様に消す冪を入力する。
使われ方：自由化のブローアップの後に余核を平坦化し、元の加群の純変換へ戻す。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory
open scoped TensorProduct

/--
概要：係数変更前に境界ねじれを除く操作は、係数変更後の純変換に影響しない。
方針：二つの商写像の合成の核を境界ねじれと同定し、その像が標的全体であることを使う。
規約：中間の純変換や追加係数変更に平坦性を仮定せず、一様な境界冪を入力する。
使われ方：Stacks 0815 で複数段の許容ブローアップを合成する。
-/
def modulePureTransform_baseChange_pureTransformEquivOfBound
    {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] (a : R) (n : ℕ)
    (hn : ∀ m ∈ boundaryTorsion a M, a ^ n • m = 0) :
    modulePureTransform (algebraMap R A a) (A ⊗[R] M) ≃ₗ[A]
      modulePureTransform (algebraMap R A a) (A ⊗[R] modulePureTransform a M) := by
  let b := algebraMap R A a
  let P := modulePureTransform a M
  let q := (boundaryTorsion a M).mkQ
  let r := (boundaryTorsion b (A ⊗[R] P)).mkQ
  let g := r.comp (q.baseChange A)
  let h := boundaryPowerLift a M n hn
  have hh : h.comp q = a ^ n • LinearMap.id := boundaryPowerLift_comp_mkQ a M n hn
  have hker (z : A ⊗[R] M) (hz : g z = 0) : ∃ k : ℕ, b ^ k • z = 0 := by
    have ht : q.baseChange A z ∈ boundaryTorsion b (A ⊗[R] P) :=
      (Submodule.Quotient.mk_eq_zero _).mp hz
    obtain ⟨k, hk⟩ := (mem_boundaryTorsion_iff b (A ⊗[R] P) _).mp ht
    have hq : q.baseChange A (b ^ k • z) = 0 := by
      rw [map_smul, hk]
    have hA := baseChange_ker_annihilated_of_scalar_leftInverse q h (a ^ n) hh _ hq
    refine ⟨n + k, ?_⟩
    rw [pow_add, mul_smul, show b ^ n = algebraMap R A (a ^ n) by exact (map_pow _ _ _).symm]
    exact hA
  let e := modulePureTransformEquivImage b g
    (modulePureTransform_isSMulRegular b (A ⊗[R] P)) hker
  have hsurj : Function.Surjective g :=
    (Submodule.mkQ_surjective _).comp
      (LinearMap.baseChange_surjective A (Submodule.mkQ_surjective (boundaryTorsion a M)))
  exact e.trans (LinearEquiv.ofTop _ (LinearMap.range_eq_top.mpr hsurj))

/--
概要：二段の係数変更で得た純変換が平坦なら、合成の純変換も平坦。
方針：最初の純変換を除く比較同型と、二段のテンソル積を一段にする同型を合成する。
規約：中間係数環上の境界ねじれを一様な冪で消せることを仮定する。
使われ方：二段の許容ブローアップを一つの中心で支配する際に平坦性を移す。
-/
theorem tensorPureTransform_flat_of_iterated_of_bound
    {R A C M : Type*} [CommRing R] [CommRing A] [CommRing C]
    [Algebra R A] [Algebra R C] [Algebra A C] [IsScalarTower R A C]
    [AddCommGroup M] [Module R M] (a : R) (n : ℕ)
    (hn : ∀ m ∈ boundaryTorsion (algebraMap R A a) (A ⊗[R] M),
      (algebraMap R A a) ^ n • m = 0)
    [Module.Flat C (modulePureTransform (algebraMap A C (algebraMap R A a))
      (C ⊗[A] modulePureTransform (algebraMap R A a) (A ⊗[R] M)))] :
    Module.Flat C (modulePureTransform (algebraMap R C a) (C ⊗[R] M)) := by
  let e := (tensorPureTransformCancelBaseChange R A C M a).symm.trans
    (modulePureTransform_baseChange_pureTransformEquivOfBound (A := C) (algebraMap R A a) n hn)
  exact Module.Flat.of_linearEquiv e


/--
概要：中間係数環上の純変換をさらに平坦化すれば、元の基底からの純変換も平坦。
方針：全アフィン試験対象で二段の純変換の比較を使う。
規約：中間の加群の境界ねじれを一様に消す冪を入力する。
使われ方：自由化の中心の上で余核を平坦化した局所中心を、元の加群の平坦化に戻す。
-/
theorem HasFlatPurePullbacks.of_iterated_of_bound
    {R A : CommRingCat.{u}} {X : Scheme.{u}} (φ : R ⟶ A) (p : X ⟶ Spec A)
    (a : R) (M : Type v) [AddCommGroup M] [Module R M]
    (n : ℕ)
    (hn : letI : Algebra R A := φ.hom.toAlgebra
      ∀ m ∈ boundaryTorsion (φ.hom a) (A ⊗[R] M), (φ.hom a) ^ n • m = 0)
    (h : letI : Algebra R A := φ.hom.toAlgebra
      HasFlatPurePullbacks p (φ.hom a) (modulePureTransform (φ.hom a) (A ⊗[R] M))) :
    HasFlatPurePullbacks (p ≫ Spec.map φ) a M := by
  intro B j
  let P (ψ : R →+* B) : Prop :=
    letI : Algebra R B := ψ.toAlgebra
    IsRegular (ψ a) → Module.Flat B (modulePureTransform (ψ a) (B ⊗[R] M))
  let θ := pureTransformCoefficientMap p j
  have hcomp : P (θ.comp φ.hom) := by
    let : Algebra R A := φ.hom.toAlgebra
    let : Algebra A B := θ.toAlgebra
    let : Algebra R B := (θ.comp φ.hom).toAlgebra
    let : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    intro ha
    let : Module.Flat B (modulePureTransform (θ (φ.hom a))
        (B ⊗[A] modulePureTransform (φ.hom a) (A ⊗[R] M))) := h B j ha
    exact tensorPureTransform_flat_of_iterated_of_bound (C := B) a n hn
  exact (congrArg P (pureTransformCoefficientMap_post_spec p φ j)).mpr hcomp

end SerrePositivity.AlgebraicGeometry
