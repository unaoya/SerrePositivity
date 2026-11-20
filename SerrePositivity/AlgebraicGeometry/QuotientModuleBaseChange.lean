module

public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
概要：KST §5、Stacks 05CG・05D3 の商環への加群の基底変更と二重剰余。
方針：商テンソル同型を商環の線形性まで強化し、二重剰余は第三同型定理で比較する。
規約：対象は通常の加群の商であり、K 理論には依存しない。
使われ方：平坦加群の各冪剰余に冪零剰余の射影性判定を適用する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

/--
概要：商環へのテンソル基底変更を、商環上の実際の線形同型としてイデアル倍による商へ移す。
方針：Mathlib の商テンソル同型を、商写像の全射性で商環の線形同型へ強化する。
規約：KST §5、Stacks 05CG・05D3、加群は任意。
使われ方：平坦性の商環への基底変更。
-/
def quotientModuleTensorEquiv
    {R : Type u} [CommRing R] (I : Ideal R) (M : Type u) [AddCommGroup M] [Module R M] :
    (R ⧸ I) ⊗[R] M ≃ₗ[R ⧸ I] M ⧸ (I • (⊤ : Submodule R M)) :=
  (TensorProduct.quotTensorEquivQuotSMul M I).extendScalarsOfSurjective
    Ideal.Quotient.mk_surjective

/--
概要：平坦加群のイデアル倍による商は、商環上平坦。
方針：テンソル基底変更の平坦性を商環線形の比較同型で移す。
規約：KST §5、Stacks 05CG・05D3、Noether 性も有限性も不要。
使われ方：各冪剰余に対する冪零剰余の射影性の平坦性仮定。
-/
theorem flat_quotientModule
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M] [Module.Flat R M]
    (I : Ideal R) : Module.Flat (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))) :=
  Module.Flat.of_linearEquiv (quotientModuleTensorEquiv I M).symm

/--
概要：商加群上で拡大イデアル倍を取った部分加群は、元のイデアル倍の像に一致する。
方針：拡大イデアル倍のスカラー制限と、全射によるイデアル倍の像の公式を使う。
規約：KST §5、Stacks 05CG・05D3、比較は元の環上の部分加群として行う。
使われ方：二重剰余の具体的な比較。
-/
theorem mappedIdeal_smul_quotient_restrictScalars
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M] (I J : Ideal R) :
    ((I.map (Ideal.Quotient.mk J)) •
      (⊤ : Submodule (R ⧸ J) (M ⧸ (J • (⊤ : Submodule R M))))).restrictScalars R =
    (I • (⊤ : Submodule R M)).map (J • (⊤ : Submodule R M)).mkQ := by
  change ((I.map (algebraMap R (R ⧸ J))) •
    (⊤ : Submodule (R ⧸ J) (M ⧸ (J • (⊤ : Submodule R M))))).restrictScalars R = _
  rw [Ideal.smul_restrictScalars, Submodule.map_smul'', Submodule.map_top,
    LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective _)]
  rfl

/--
概要：小さいイデアルで割った後に大きい拡大イデアルで割ると、大きいイデアルでの剰余になる。
方針：スカラー制限した商、拡大イデアル倍の像との一致、加群の第三同型定理を合成する。
規約：KST §5、Stacks 05CG・05D3、同型は元の環上で与える。
使われ方：各冪剰余をさらに I で割った加群の比較。
-/
def nestedQuotientModuleEquiv
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (I J : Ideal R) (hJI : J ≤ I) :
    ((M ⧸ (J • (⊤ : Submodule R M))) ⧸
      ((I.map (Ideal.Quotient.mk J)) •
        (⊤ : Submodule (R ⧸ J) (M ⧸ (J • (⊤ : Submodule R M)))))) ≃ₗ[R]
      (M ⧸ (I • (⊤ : Submodule R M))) :=
  (Submodule.Quotient.restrictScalarsEquiv R _).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (mappedIdeal_smul_quotient_restrictScalars I J) ≪≫ₗ
      Submodule.quotientQuotientEquivQuotient _ _ (Submodule.smul_mono_left hJI)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
