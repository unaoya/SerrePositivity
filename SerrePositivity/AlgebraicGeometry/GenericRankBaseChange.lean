module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.GenericPrimeBaseChange
public import SerrePositivity.AlgebraicGeometry.FreeStalkRankBaseChange

/-!
概要：KST §5、Stacks 0810・0811 の相対平坦加群の一般階数の基底変更。
方針：拡大素点の縮約と自由な局所階数の基底変更を接続する。
規約：代数の実分裂は入力し、係数環の平坦性は不要。
使われ方：階数の開閉部分を分離した実チャート上で一定一般階数を照合する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry
open scoped TensorProduct

variable (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C] [IsNoetherianRing A] [IsNoetherianRing C]
  [Module.Flat A B] [Algebra.FinitePresentation A B]
  [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
  {M ι : Type*} [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
  [Module.Flat A M] [Module.FinitePresentation B M]

/--
概要：相対平坦有限表示加群の基底変更後の一般局所階数は、元の一般局所階数の引き戻し。
方針：拡大素点の縮約を照合し、元の拡大素点での自由性に局所階数の保存を適用する。
規約：KST §5、Stacks 0810・0811、基底変更は平坦と仮定しない。
使われ方：開閉分離中心の実チャートで階数を一定にする。
-/
theorem generic_rankAtStalk_baseChange
    (e : B →ₗ[A] (ι →₀ A)) (p : (ι →₀ A) →ₗ[A] B)
    (hpe : p.comp e = LinearMap.id) (P : PrimeSpectrum C) :
    let D := C ⊗[A] B
    letI : Algebra B D := Algebra.TensorProduct.rightAlgebra
    letI : GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap C D))) :=
      geometricallyIntegral_tensorProjection A B C
    Module.rankAtStalk (D ⊗[B] M) (geometricallyIntegralGenericPrime C D P) =
      Module.rankAtStalk M
        (geometricallyIntegralGenericPrime A B (PrimeSpectrum.comap (algebraMap A C) P)) := by
  let D := C ⊗[A] B
  let : Algebra B D := Algebra.TensorProduct.rightAlgebra
  let : GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap C D))) :=
    geometricallyIntegral_tensorProjection A B C
  have hQ : PrimeSpectrum.comap (algebraMap B D) (geometricallyIntegralGenericPrime C D P) =
      geometricallyIntegralGenericPrime A B (PrimeSpectrum.comap (algebraMap A C) P) :=
    geometricallyIntegralGenericPrime_baseChange_comap A B C e p hpe P
  rw [← hQ]
  apply rankAtStalk_baseChange_of_mem_freeLocus
  rw [hQ]
  let Q := geometricallyIntegralGenericPrime A B (PrimeSpectrum.comap (algebraMap A C) P)
  exact (Module.mem_freeLocus_iff_tensor (M := M) Q (Localization.AtPrime Q.asIdeal)).mpr
    (free_at_geometricallyIntegralGenericPrime A B _)

/--
概要：相対平坦有限表示加群の一般点のテンソル局所化で計算した階数は任意の基底変更で保たれる。
方針：局所階数をテンソル局所化の有限階数に書き換える。
規約：KST §5、Stacks 0810・0811、実分裂を明示する。
使われ方：一定一般階数の係数中心の入力を実チャートで照合する。
-/
theorem generic_finrank_tensor_baseChange
    (e : B →ₗ[A] (ι →₀ A)) (p : (ι →₀ A) →ₗ[A] B)
    (hpe : p.comp e = LinearMap.id) (P : PrimeSpectrum C) :
    let D := C ⊗[A] B
    letI : Algebra B D := Algebra.TensorProduct.rightAlgebra
    letI : GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap C D))) :=
      geometricallyIntegral_tensorProjection A B C
    let L := Localization.AtPrime (geometricallyIntegralGenericPrime C D P).asIdeal
    let L₀ := Localization.AtPrime
      (geometricallyIntegralGenericPrime A B (PrimeSpectrum.comap (algebraMap A C) P)).asIdeal
    Module.finrank L (L ⊗[D] (D ⊗[B] M)) = Module.finrank L₀ (L₀ ⊗[B] M) := by
  dsimp only
  let D := C ⊗[A] B
  let : Algebra B D := Algebra.TensorProduct.rightAlgebra
  let : GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap C D))) :=
    geometricallyIntegral_tensorProjection A B C
  rw [← Module.rankAtStalk_eq_finrank_tensorProduct,
    generic_rankAtStalk_baseChange A B C e p hpe,
    Module.rankAtStalk_eq_finrank_tensorProduct]

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
