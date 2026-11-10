module

public import SerrePositivity.AlgebraicGeometry.FiniteTypePureTransformGluing
public import SerrePositivity.AlgebraicGeometry.IteratedPureTransform
public import SerrePositivity.AlgebraicGeometry.TensorAlgebraBoundaryTorsion

/-!
概要：最初のブローアップの純変換を局所中心で平坦化した結果を、一つの元の基底中心にまとめる。
方針：二段の純変換を直接の純変換へ移し、既存のアフィン局所中心の貼り合わせを使う。
規約：基底は Noether、境界元は正則、加群は有限型代数上有限とする。
使われ方：Stacks 0815 で自由化を先に行い、そのチャート上で余核に帰納を適用する。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open scoped TensorProduct

set_option maxHeartbeats 500000 in
-- 二段の斉次局所化の係数環とテンソル積の型を比較する。
/--
概要：最初の中心の各生成元チャートで純変換の局所平坦化中心があれば、一つの元の基底中心で平坦化できる。
方針：チャートごとに境界ねじれを消す一様な冪を取り、二段の純変換を比較する。
規約：局所中心と最初の中心はいずれも境界外で自明とする。
使われ方：Stacks 0815 の二段の中心を合成する。
-/
theorem exists_affine_finiteType_flatPure_center_of_iterated_local_centers
    {R : Type u} [CommRing R] [IsNoetherianRing R] (B : Type z) [CommRing B]
    [Algebra R B] [Algebra.FiniteType R B]
    (I : Ideal R) {ι : Type w} [Finite ι] (c : ι → I)
    (hc : Ideal.span (Set.range (fun i => (c i).val)) = I)
    (a : R) (ha : a ∈ nonZeroDivisors R) (M : Type v)
    [AddCommGroup M] [Module R M] [Module B M] [IsScalarTower R B M] [Module.Finite B M]
    (hI : PrimeSpectrum.basicOpen a ≤ affineCenterComplement I)
    (K : ∀ i, Ideal (BlowupChartRing I (c i)))
    (hK : ∀ i, PrimeSpectrum.basicOpen (chartBaseMap I (c i) a) ≤ affineCenterComplement (K i))
    (hflat : ∀ (i) (b : K i),
      let A := BlowupChartRing I (c i)
      let C := BlowupChartRing (K i) b
      let φ := chartBaseMap I (c i)
      let ψ := chartBaseMap (K i) b
      letI : Algebra R A := φ.toAlgebra
      letI : Algebra A C := ψ.toAlgebra
      Module.Flat C (modulePureTransform (ψ (φ a))
        (C ⊗[A] modulePureTransform (φ a) (A ⊗[R] M)))) :
    ∃ J : Ideal R, J.FG ∧ PrimeSpectrum.basicOpen a ≤ affineCenterComplement J ∧
      ∀ b : J, letI : Algebra R (BlowupChartRing J b) := (chartBaseMap J b).toAlgebra
        Module.Flat (BlowupChartRing J b)
          (modulePureTransform (chartBaseMap J b a) (BlowupChartRing J b ⊗[R] M)) := by
  apply exists_affine_finiteType_flatPure_center_of_local_centers B I c hc a ha M hI K hK
  intro i b
  let A := BlowupChartRing I (c i)
  let C := BlowupChartRing (K i) b
  let φ := chartBaseMap I (c i)
  let ψ := chartBaseMap (K i) b
  let : Algebra R A := φ.toAlgebra
  let : Algebra A C := ψ.toAlgebra
  let : Algebra R C := (ψ.comp φ).toAlgebra
  let : @IsScalarTower R A C (inferInstance : Algebra R A).toSMul
      (inferInstance : Algebra A C).toSMul (inferInstance : Algebra R C).toSMul :=
    IsScalarTower.of_algebraMap_eq' (R := R) (S := A) (A := C) rfl
  let : IsNoetherianRing A := blowupChartRing_isNoetherianRing I (c i)
  obtain ⟨n, hn⟩ := tensorAlgebraModule_boundaryTorsion_bounded R B A M (φ a)
  let : Module.Flat C (modulePureTransform (ψ (φ a))
      (C ⊗[A] modulePureTransform (φ a) (A ⊗[R] M))) := hflat i b
  exact tensorPureTransform_flat_of_iterated_of_bound (C := C) a n hn

end SerrePositivity.AlgebraicGeometry
