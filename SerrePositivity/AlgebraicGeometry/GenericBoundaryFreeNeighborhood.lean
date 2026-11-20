module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.GenericBoundaryFreeLocus

/-!
概要：KST §5、Stacks 0810 の一般点を含む基本開近傍での純変換の自由性。
方針：局所化の比較で階数を照合し、有限表示加群の自由基底を基本開へ降ろす。
規約：純変換の対象とその共通自由階数を保持する。
使われ方：係数中心の各チャートで具体的な自由化元を得る。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry
open scoped TensorProduct

/--
概要：有限表示加群の自由な素点には同じ階数で自由となる基本開近傍が存在する。
方針：素点局所化の自由基底を一元局所化へ降ろす。
規約：KST §5、Stacks 0810、加群の全体での平坦性は不要。
使われ方：一般点自由性を実際の自由化元の存在に変換する。
-/
theorem exists_away_free_finrank_of_mem_freeLocus
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M] (P : PrimeSpectrum R) (hP : P ∈ Module.freeLocus R M) :
    ∃ g ∉ P.asIdeal,
      Module.Free (Localization.Away g) (LocalizedModule.Away g M) ∧
        Module.finrank (Localization.Away g) (LocalizedModule.Away g M) =
          Module.rankAtStalk M P := by
  let : Module.Free (Localization.AtPrime P.asIdeal)
      (LocalizedModule P.asIdeal.primeCompl M) := Module.mem_freeLocus.mp hP
  exact Module.FinitePresentation.exists_free_localizedModule_powers P.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap P.asIdeal.primeCompl M) (Localization.AtPrime P.asIdeal)

variable (A B C : Type u) (M : Type*) [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C] [IsNoetherianRing C] [Module.Flat A B]
  [Algebra.FinitePresentation A B]
  [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
  [AddCommGroup M] [Module B M]

/--
概要：全拡大素点での境界純変換の共通自由階数は実際の純変換の局所階数と一致する。
方針：素点局所化比較とテンソル取消による二つの線形同型で有限階数を運ぶ。
規約：KST §5、Stacks 0810、代数の作用は一般点自由性の述語と一致させる。
使われ方：基本開自由化の階数を元の共通階数に固定する。
-/
theorem genericPrime_rankAtStalk_of_genericBoundaryPureFree (f : C) (r : ℕ)
    (hGF : GenericBoundaryPureFree A B C M f r) (P : PrimeSpectrum C) :
    let D := C ⊗[A] B
    letI : Algebra B D := Algebra.TensorProduct.rightAlgebra
    letI : GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap C D))) :=
      geometricallyIntegral_tensorProjection A B C
    Module.rankAtStalk (modulePureTransform (algebraMap C D f) (D ⊗[B] M))
      (geometricallyIntegralGenericPrime C D P) = r := by
  let D := C ⊗[A] B
  let : Algebra B D := Algebra.TensorProduct.rightAlgebra
  let : GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap C D))) :=
    geometricallyIntegral_tensorProjection A B C
  let Q := geometricallyIntegralGenericPrime C D P
  let L := Localization.AtPrime Q.asIdeal
  let φ : B →+* L := (algebraMap D L).comp
    (Algebra.TensorProduct.includeRight : B →ₐ[A] D).toRingHom
  let : Algebra B L := φ.toAlgebra
  let : Module B L := φ.toAlgebra.toModule
  let : @IsScalarTower B D L (inferInstance : Algebra B D).toSMul
      (inferInstance : Algebra D L).toSMul (inferInstance : Algebra B L).toSMul :=
    IsScalarTower.of_algebraMap_eq' (R := B) (S := D) (A := L) rfl
  let N := D ⊗[B] M
  let d := algebraMap C D f
  let E : (L ⊗[D] N) ≃ₗ[L] (L ⊗[B] M) :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange B D L L M
  calc
    Module.rankAtStalk (modulePureTransform d N) Q =
        Module.finrank L (modulePureTransform (algebraMap D L d) (L ⊗[D] N)) :=
      (pureTransformAtPrimeTensorEquiv (M := N) Q.asIdeal d).finrank_eq
    _ = Module.finrank L (modulePureTransform (algebraMap D L d) (L ⊗[B] M)) :=
      (modulePureTransformCongr (algebraMap D L d) E).finrank_eq
    _ = r := (hGF P).2

/--
概要：一般点で自由な有限加群の境界純変換は各基礎素点上のある基本開で同じ階数の自由加群。
方針：拡大素点の自由 locus への所属と局所階数を使い、自由基底を基本開へ降ろす。
規約：KST §5、Stacks 0810, Lemma 38.30.2、基礎環は Noether。
使われ方：係数 blowup の各チャートで具体的な自由化元 g を選ぶ。
-/
theorem exists_away_free_finrank_of_genericBoundaryPureFree [Module.Finite B M]
    (f : C) (r : ℕ) (hGF : GenericBoundaryPureFree A B C M f r) (P : PrimeSpectrum C) :
    let D := C ⊗[A] B
    letI : Algebra B D := Algebra.TensorProduct.rightAlgebra
    let G := modulePureTransform (algebraMap C D f) (D ⊗[B] M)
    ∃ g ∉ P.asIdeal.map (algebraMap C D),
      Module.Free (Localization.Away g) (LocalizedModule.Away g G) ∧
        Module.finrank (Localization.Away g) (LocalizedModule.Away g G) = r := by
  let D := C ⊗[A] B
  let : Algebra B D := Algebra.TensorProduct.rightAlgebra
  let G := modulePureTransform (algebraMap C D f) (D ⊗[B] M)
  let : IsNoetherianRing D := Algebra.FiniteType.isNoetherianRing C D
  let : Module.FinitePresentation D G := Module.finitePresentation_of_finite D G
  let : GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap C D))) :=
    geometricallyIntegral_tensorProjection A B C
  obtain ⟨g, hg, hfree, hr⟩ := exists_away_free_finrank_of_mem_freeLocus
    (geometricallyIntegralGenericPrime C D P)
    (genericPrime_mem_freeLocus_of_genericBoundaryPureFree A B C M f r hGF P)
  exact ⟨g, hg, hfree, hr.trans
    (genericPrime_rankAtStalk_of_genericBoundaryPureFree A B C M f r hGF P)⟩

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
