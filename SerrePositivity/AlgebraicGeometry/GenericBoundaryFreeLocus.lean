module

public import SerrePositivity.AlgebraicGeometry.GenericBoundaryPureFree
public import SerrePositivity.AlgebraicGeometry.GeometricallyIntegralGenericFreeness
public import SerrePositivity.AlgebraicGeometry.PureTransformStalkEquiv
public import SerrePositivity.AlgebraicGeometry.PureTransformCongr
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
概要：KST §5、Stacks 0810・0811 の一般点で自由な純変換の開自由 locus。
方針：局所化比較とテンソル取消同型で自由 locus の所属を証明し、拡大素点の縮約で基礎環を覆う。
規約：純変換は実際の基底変更加群の境界ねじれによる商とする。
使われ方：係数中心のチャート上で基礎環へ全射な自由な開部分を作る。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry
open scoped TensorProduct

variable (A B C : Type u) (M : Type*) [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C] [IsNoetherianRing C] [Module.Flat A B]
  [Algebra.FinitePresentation A B]
  [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
  [AddCommGroup M] [Module B M]

/--
概要：一般点での境界純変換の自由性は実際の基底変更加群の純変換の自由 locus への所属を与える。
方針：純変換の素点局所化比較と二段テンソル取消の実同型で自由性を運ぶ。
規約：KST §5、Stacks 0810, Lemma 38.30.2・0811, Lemma 38.30.3、代数作用を明示する。
使われ方：全拡大素点が純変換の開自由 locus に入ることを示す。
-/
theorem genericPrime_mem_freeLocus_of_genericBoundaryPureFree (f : C) (r : ℕ)
    (hGF : GenericBoundaryPureFree A B C M f r) (P : PrimeSpectrum C) :
    let D := C ⊗[A] B
    letI : Algebra B D := Algebra.TensorProduct.rightAlgebra
    letI : GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap C D))) :=
      geometricallyIntegral_tensorProjection A B C
    geometricallyIntegralGenericPrime C D P ∈
      Module.freeLocus D (modulePureTransform (algebraMap C D f) (D ⊗[B] M)) := by
  let D := C ⊗[A] B
  let : Algebra B D := Algebra.TensorProduct.rightAlgebra
  let : GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap C D))) :=
    geometricallyIntegral_tensorProjection A B C
  let Q := geometricallyIntegralGenericPrime C D P
  let L := Localization.AtPrime Q.asIdeal
  let φB : B →+* D := (Algebra.TensorProduct.includeRight : B →ₐ[A] D).toRingHom
  let φ : B →+* L := (algebraMap D L).comp φB
  let : Algebra B L := φ.toAlgebra
  let : Module B L := φ.toAlgebra.toModule
  let : @IsScalarTower B D L (inferInstance : Algebra B D).toSMul
      (inferInstance : Algebra D L).toSMul (inferInstance : Algebra B L).toSMul :=
    IsScalarTower.of_algebraMap_eq' (R := B) (S := D) (A := L) rfl
  let N := D ⊗[B] M
  let d := algebraMap C D f
  let : Module.Free L (modulePureTransform (algebraMap D L d) (L ⊗[B] M)) := (hGF P).1
  let E : (L ⊗[D] N) ≃ₗ[L] (L ⊗[B] M) :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange B D L L M
  let : Module.Free L (modulePureTransform (algebraMap D L d) (L ⊗[D] N)) :=
    Module.Free.of_equiv (modulePureTransformCongr (algebraMap D L d) E).symm
  exact mem_freeLocus_pureTransform_of_tensorPureFree (M := N) Q d

/--
概要：有限な基底変更加群の純変換の自由 locus は開で、全一般点で自由なら基礎環を覆う。
方針：Noether 性から有限表示性を得て自由 locus を開とし、拡大素点の縮約で像の全射性を示す。
規約：KST §5、Stacks 0810・0811、元の加群の有限性は代数 B 上に課す。
使われ方：係数 blowup チャートで基礎環へ全射な自由な開部分を得る。
-/
theorem isOpen_freeLocus_and_image_eq_univ_of_genericBoundaryPureFree [Module.Finite B M]
    (f : C) (r : ℕ) (hGF : GenericBoundaryPureFree A B C M f r) :
    let D := C ⊗[A] B
    letI : Algebra B D := Algebra.TensorProduct.rightAlgebra
    let G := modulePureTransform (algebraMap C D f) (D ⊗[B] M)
    IsOpen (Module.freeLocus D G) ∧
      (PrimeSpectrum.comap (algebraMap C D)) '' (Module.freeLocus D G) = Set.univ := by
  let D := C ⊗[A] B
  let : Algebra B D := Algebra.TensorProduct.rightAlgebra
  let G := modulePureTransform (algebraMap C D f) (D ⊗[B] M)
  let : IsNoetherianRing D := Algebra.FiniteType.isNoetherianRing C D
  let : Module.FinitePresentation D G := Module.finitePresentation_of_finite D G
  let : GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap C D))) :=
    geometricallyIntegral_tensorProjection A B C
  refine ⟨Module.isOpen_freeLocus, ?_⟩
  apply Set.eq_univ_iff_forall.mpr
  intro P
  refine ⟨geometricallyIntegralGenericPrime C D P, ?_, ?_⟩
  · exact genericPrime_mem_freeLocus_of_genericBoundaryPureFree A B C M f r hGF P
  · exact geometricallyIntegralGenericPrime_comap C D P

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
