module

public import SerrePositivity.AlgebraicGeometry.GeometricallyIntegralGenericFreeness
public import SerrePositivity.AlgebraicGeometry.SplitAlgebraFiberRegularity

/-!
概要：KST §5、Stacks 05DH・0810 の幾何学的整な代数での特殊な局所化の単射性。
方針：体への基底変更の幾何学的整性からファイバー環の整域性を得る。
規約：分裂の存在は実際の線形写像として明示する。
使われ方：高次小行列式を特別な局所化で検出する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry
open scoped TensorProduct

/--
概要：幾何学的整な代数を任意の体へ基底変更した実際のテンソル積環は整域。
方針：基底変更後の Spec の整性を体上の幾何学的整性から導く。
規約：KST §5、Stacks 05DH・0810、この段階は Noether 性や分裂を使わない。
使われ方：局所環の閉ファイバーでの乗法の単射性。
-/
theorem isDomain_tensor_of_geometricallyIntegral
    (A B K : Type u) [CommRing A] [CommRing B] [Field K] [Algebra A B] [Algebra A K]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap A B)))] :
    IsDomain (K ⊗[A] B) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[A] B)))
  have : GeometricallyIntegral f := geometricallyIntegral_tensorProjection A B K
  have : IsIntegral (Spec (.of (K ⊗[A] B))) :=
    GeometricallyIntegral.isIntegral_of_subsingleton f
  exact (affine_isIntegral_iff (.of (K ⊗[A] B))).mp inferInstance

/--
概要：幾何学的整な分裂代数では拡大極大イデアルの外の元は正則。
方針：幾何学的整性から閉ファイバーの整域性を導き、剰余体による正則性判定を使う。
規約：KST §5、Stacks 05DH・0810、基礎環の局所性と実際の分裂を明示する。
使われ方：特別な局所化で許される分母が非零因子となることを確かめる。
-/
theorem geometricallyIntegral_split_isRegular_of_not_mem_extended_maximalIdeal
    (A B : Type u) [CommRing A] [IsLocalRing A] [CommRing B] [Algebra A B]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
    {ι : Type*} (e : B →ₗ[A] (ι →₀ A)) (p : (ι →₀ A) →ₗ[A] B)
    (hpe : p.comp e = LinearMap.id) (s : B)
    (hs : s ∉ (IsLocalRing.maximalIdeal A).map (algebraMap A B)) : IsRegular s := by
  let : IsDomain ((IsLocalRing.ResidueField A) ⊗[A] B) :=
    isDomain_tensor_of_geometricallyIntegral A B (IsLocalRing.ResidueField A)
  exact splitAlgebra_isRegular_of_not_mem_extended_maximalIdeal e p hpe s hs

/--
概要：Noether 局所環上の幾何学的整な分裂代数から拡大極大素点での局所化への写像は単射。
方針：既証の拡大素性で対象を構成し、閉ファイバーの整域性による分母の正則性を使う。
規約：KST §5、Stacks 05DH・0810、平坦有限表示性と実際の分裂を明示する。
使われ方：表示行列の高次小行列式の消滅を特別な局所環へ移して調べる。
-/
theorem geometricallyIntegral_split_extendedMaximalLocalization_injective
    (A B : Type u) [CommRing A] [IsLocalRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Module.Flat A B] [Algebra.FinitePresentation A B]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
    {ι : Type*} (e : B →ₗ[A] (ι →₀ A)) (p : (ι →₀ A) →ₗ[A] B)
    (hpe : p.comp e = LinearMap.id) :
    Function.Injective (algebraMap B (Localization.AtPrime
      (geometricallyIntegralGenericPrime A B
        ⟨IsLocalRing.maximalIdeal A, inferInstance⟩).asIdeal)) := by
  let : IsDomain ((IsLocalRing.ResidueField A) ⊗[A] B) :=
    isDomain_tensor_of_geometricallyIntegral A B (IsLocalRing.ResidueField A)
  let : ((IsLocalRing.maximalIdeal A).map (algebraMap A B)).IsPrime :=
    ideal_map_isPrime_of_geometricallyIntegral A B (IsLocalRing.maximalIdeal A)
  exact splitAlgebra_extendedMaximalLocalization_injective e p hpe

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
