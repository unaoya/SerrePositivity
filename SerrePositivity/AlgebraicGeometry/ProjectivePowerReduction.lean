module

public import SerrePositivity.AlgebraicGeometry.QuotientModuleBaseChange
public import SerrePositivity.AlgebraicGeometry.NilpotentProjectivity
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
概要：KST §5、Stacks 05D3 の平坦加群の各冪剰余の射影性。
方針：二重剰余を商環の第三同型定理に沿った半線形同型で比較し、冪零剰余の判定を適用する。
規約：元の I による剰余の射影性だけを仮定する。
使われ方：完備化の右逆を作る各有限段階の持ち上げ。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/--
概要：二重剰余の比較の逆は、商環の第三同型定理の逆に関する半線形同型。
方針：元の環の代表元の作用で線形性を確認する。
規約：KST §5、Stacks 05CG・05D3、半線形性の係数写像を明示する。
使われ方：二重剰余の射影性を対応する商環上へ移す。
-/
def nestedQuotientModuleSemilinearEquiv
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (I J : Ideal R) (hJI : J ≤ I) :
    (M ⧸ (I • (⊤ : Submodule R M))) ≃ₛₗ[
      RingHomClass.toRingHom (DoubleQuot.quotQuotEquivQuotOfLE hJI).symm]
    ((M ⧸ (J • (⊤ : Submodule R M))) ⧸
      ((I.map (Ideal.Quotient.mk J)) •
        (⊤ : Submodule (R ⧸ J) (M ⧸ (J • (⊤ : Submodule R M)))))) where
  __ := (nestedQuotientModuleEquiv I J hJI).symm.toAddEquiv
  map_smul' a x := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    change (nestedQuotientModuleEquiv I J hJI).symm (r • x) =
      (DoubleQuot.quotQuotEquivQuotOfLE hJI).symm (Ideal.Quotient.mk I r) •
        (nestedQuotientModuleEquiv I J hJI).symm x
    rw [DoubleQuot.quotQuotEquivQuotOfLE_symm_mk]
    exact (nestedQuotientModuleEquiv I J hJI).symm.map_smul r x

/--
概要：I による剰余が射影的なら、小さい J による剰余を拡大 I で割った加群も射影的。
方針：明示した商環の同型に沿う半線形同型で射影性を移す。
規約：KST §5、Stacks 05CG・05D3、平坦性はこの移送には不要。
使われ方：冪零剰余の射影性判定の射影性仮定。
-/
theorem projective_nestedQuotientModule
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (I J : Ideal R) (hJI : J ≤ I)
    [Module.Projective (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M)))] :
    Module.Projective ((R ⧸ J) ⧸ I.map (Ideal.Quotient.mk J))
      ((M ⧸ (J • (⊤ : Submodule R M))) ⧸
        ((I.map (Ideal.Quotient.mk J)) •
          (⊤ : Submodule (R ⧸ J) (M ⧸ (J • (⊤ : Submodule R M)))))) :=
  Module.Projective.of_equiv (σ' := RingHomClass.toRingHom (DoubleQuot.quotQuotEquivQuotOfLE hJI))
    (nestedQuotientModuleSemilinearEquiv I J hJI)

/--
概要：平坦加群の I による剰余が射影的なら、各正の冪による剰余も対応する商環上射影的。
方針：商環への平坦性の基底変更と二重剰余の射影性に、冪零剰余の判定を適用する。
規約：KST §5、Stacks 05D3, Lemma 10.97.9、Noether 性を課さない。
使われ方：完備化の分裂の整合的な右逆の各段階。
-/
theorem projective_powerQuotientModule
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M] [Module.Flat R M]
    (I : Ideal R) [Module.Projective (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M)))]
    (n : ℕ) (hn : n ≠ 0) :
    Module.Projective (R ⧸ I ^ n) (M ⧸ (I ^ n • (⊤ : Submodule R M))) := by
  let := flat_quotientModule (M := M) (I ^ n)
  let := projective_nestedQuotientModule (M := M) I (I ^ n) (Ideal.pow_le_self hn)
  apply projective_of_flat_of_projective_nilpotent_reduction
    (I.map (Ideal.Quotient.mk (I ^ n))) n
  rw [← Ideal.map_pow, Ideal.map_quotient_self]
  rfl

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
