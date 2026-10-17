module

public import SerrePositivity.BhattScholze.Andre.CompletelyFlatRegularReduction
public import SerrePositivity.CommutativeAlgebra.CompletelyFlatCriterion
public import SerrePositivity.CommutativeAlgebra.PrincipalAdicFaithfulDescent

/-!
# André E1・E2：正則主環商から二元完全平坦性を戻す

## 概要

可換代数の正則主環商の完全平坦性を、元の係数作用に関する二元完全平坦性へ移す。
BS Rem 7.15（著者版 p.62）の自然な実候補の導来剰余への接続。

## 方針

標準スカラー拡大と通常主環商の線形同型を作り、正則主剰余の一般判定を使う。

## 規約

基底環と代数での分母正則性を明示する。通常平坦性や Noether 性は不要。

## 使われ方

自然な Hodge–Tate 候補の p 完全平坦性を元の実完備化の (p,d) 完全平坦性へ戻す。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory
attribute [local instance] principalAdicQuotientAlgebra

/-- 概要：標準主剰余スカラー拡大は代数の通常主環商と剰余基底上線形同型。
方針：標準加群商への比較と通常主環商への比較を合成する。
規約：正則性を必要としない。
使われ方：BS Rem 7.15（著者版 p.62）の自然な剰余作用の照合。 -/
def principalScalarExtensionAlgebraQuotientEquiv
    {R : Type u} [CommRing R] (d : R) (S : Type u) [CommRing S] [Algebra R S] :
    ((ModuleCat.extendScalars (Ideal.Quotient.mk (Ideal.span {d}))).obj (ModuleCat.of R S)) ≃ₗ[
      R ⧸ Ideal.span {d}] (S ⧸ Ideal.span {algebraMap R S d}) :=
  (quotientScalarExtensionEquiv (Ideal.span {d}) (ModuleCat.of R S)).trans
    (principalAdicReductionEquiv d S)

/-- 概要：正則な主環商の a 完全平坦性は元の代数の (a,d) 完全平坦性を与える。
方針：通常主商を標準剰余スカラー拡大へ移して一般判定へ渡す。
規約：通常主商の係数作用は標準商代数構造。
使われ方：BS Rem 7.15（著者版 p.62）の実完備化の導来剰余の入力。 -/
theorem completelyFlat_pair_algebra_of_regular_reduction
    {R : Type u} [CommRing R] (a d : R) (hd : IsSMulRegular R d)
    (S : Type u) [CommRing S] [Algebra R S] (hSd : IsSMulRegular S (algebraMap R S d))
    (hred : IsCompletelyFlat (Ideal.span {Ideal.Quotient.mk (Ideal.span {d}) a})
      (S ⧸ Ideal.span {algebraMap R S d})) :
    IsCompletelyFlat (Ideal.span {a, d}) S := by
  have hMd : IsSMulRegular (ModuleCat.of R S) d := by
    intro x y hxy
    apply hSd
    simpa only [Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply] using hxy
  have hM := isCompletelyFlat_of_linearEquiv _
    (principalScalarExtensionAlgebraQuotientEquiv d S).symm hred
  exact completelyFlat_pair_of_regular_principal_reduction a d hd (ModuleCat.of R S) hMd hM

end SerrePositivity.BhattScholze.Andre
