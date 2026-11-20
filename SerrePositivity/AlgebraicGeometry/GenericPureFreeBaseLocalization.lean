module

public import SerrePositivity.AlgebraicGeometry.TensorAlgebraBaseLocalization
public import SerrePositivity.AlgebraicGeometry.FreeLocusLocalizedModule
public import SerrePositivity.AlgebraicGeometry.GenericPrimePushout
public import SerrePositivity.AlgebraicGeometry.BoundaryFreeOpensGenericFree

/-!
概要：KST §5、Stacks 0811 の係数局所化による純変換の一般点自由性の正確な比較。
方針：明示的な押し出しで一般点を縮約し、純変換の係数局所化の自由 locus を比較する。
規約：元の代数と加群を保持し、局所化後の境界の正則性は要求しない。
使われ方：基礎環の基本開ごとの自由化を開被覆に沿って大域化する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry
open scoped TensorProduct

/--
概要：係数局所化後の拡大一般点での純変換の自由性は、縮約基礎素点の拡大一般点での自由性と同値。
方針：局所化の押し出しにおける一般点の縮約と、純変換の局所化の自由 locus の比較を合成する。
規約：KST §5、Stacks 0811、Noether 係数環と元の代数の実分裂を入力する。
使われ方：自由化基本開の存在を係数環の基本開から戻す。
-/
theorem genericPureTransformFree_baseLocalization_iff
    (A B C E : Type u) (M : Type*) [CommRing A] [CommRing B] [CommRing C] [CommRing E]
    [Algebra A B] [Algebra A C] [Algebra A E] [Algebra C E] [IsScalarTower A C E]
    [IsNoetherianRing C] [IsNoetherianRing E]
    [Module.Flat A B] [Algebra.FinitePresentation A B]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
    [AddCommGroup M] [Module B M] {ι : Type*}
    (e : B →ₗ[A] (ι →₀ A)) (p : (ι →₀ A) →ₗ[A] B) (hpe : p.comp e = LinearMap.id)
    (S : Submonoid C) [IsLocalization S E] (f : C) (P : PrimeSpectrum E) :
    let D := C ⊗[A] B
    let F := E ⊗[A] B
    letI : Algebra B D := Algebra.TensorProduct.rightAlgebra
    letI : Algebra B F := Algebra.TensorProduct.rightAlgebra
    letI : GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap C D))) :=
      geometricallyIntegral_tensorProjection A B C
    letI : GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap E F))) :=
      geometricallyIntegral_tensorProjection A B E
    geometricallyIntegralGenericPrime E F P ∈
        Module.freeLocus F (modulePureTransform (algebraMap E F (algebraMap C E f)) (F ⊗[B] M)) ↔
      geometricallyIntegralGenericPrime C D (P.comap (algebraMap C E)) ∈
        Module.freeLocus D (modulePureTransform (algebraMap C D f) (D ⊗[B] M)) := by
  dsimp only
  let D := C ⊗[A] B
  let F := E ⊗[A] B
  let : Algebra B D := Algebra.TensorProduct.rightAlgebra
  let : Algebra B F := Algebra.TensorProduct.rightAlgebra
  let : Algebra C F := ((algebraMap E F).comp (algebraMap C E)).toAlgebra
  let : Algebra D F := (tensorAlgebraBaseChangeMap A B C E).toRingHom.toAlgebra
  let : @IsScalarTower C E F (inferInstance : Algebra C E).toSMul
      (inferInstance : Algebra E F).toSMul (inferInstance : Algebra C F).toSMul :=
    IsScalarTower.of_algebraMap_eq' (R := C) (S := E) (A := F) rfl
  let : @IsScalarTower C D F (inferInstance : Algebra C D).toSMul
      (inferInstance : Algebra D F).toSMul (inferInstance : Algebra C F).toSMul :=
    tensorAlgebraBaseChange_isScalarTower_left_algebra A B C E
  let : IsScalarTower B D F := tensorAlgebraBaseChange_isScalarTower_right A B C E
  let : Algebra.IsPushout C E D F := tensorAlgebraBaseChange_isPushout A B C E
  let : IsLocalization (Algebra.algebraMapSubmonoid D S) F :=
    tensorAlgebraBaseChange_isLocalization A B C E S
  let : GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap C D))) :=
    geometricallyIntegral_tensorProjection A B C
  let : GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap E F))) :=
    geometricallyIntegral_tensorProjection A B E
  let e' := splitAlgebraTensorEmbedding (C := C) e
  let p' := splitAlgebraTensorRetraction (C := C) p
  have hs : p'.comp e' = LinearMap.id := splitAlgebraTensorRetraction_comp_embedding e p hpe
  have hQ := geometricallyIntegralGenericPrime_pushout_comap C D E F e' p' hs P
  have hscalar : algebraMap D F (algebraMap C D f) =
      algebraMap E F (algebraMap C E f) := by
    change tensorAlgebraBaseChangeMap A B C E (algebraMap C D f) = _
    exact tensorAlgebraBaseChangeMap_left A B C E f
  have h := mem_freeLocus_tensorPureTransform_iff_of_isLocalization B D F M
    (Algebra.algebraMapSubmonoid D S) (algebraMap C D f)
    (geometricallyIntegralGenericPrime E F P)
  rwa [hscalar, hQ] at h

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
