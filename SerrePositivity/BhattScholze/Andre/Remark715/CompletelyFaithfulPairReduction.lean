module

public import SerrePositivity.BhattScholze.Andre.Remark715.CompletelyFlatRegularAlgebraReduction
public import SerrePositivity.BhattScholze.Andre.Remark715.PerfectPrismVarpi

/-!
# André E1・E2：二段の主剰余の忠実平坦性

## 概要

主剰余の完全忠実平坦性から元の二元剰余の忠実平坦性を得る。
BS Rem 7.15（著者版 p.62）の導来剰余 H⁰ の準備。

## 方針

標準スカラー拡大を二段に分け、二重主商の係数同型に沿って忠実平坦性を底変換する。

## 規約

本工程では正則性を使わず、通常の剰余加群だけを扱う。

## 使われ方

自然な H/d の p 完全忠実平坦性から H の (p,d) 剰余の忠実平坦性へ進む。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory
open scoped TensorProduct

/-- 概要：完全忠実平坦性は標準スカラー拡大の忠実平坦性を与える。
方針：定義中の通常テンソルと標準剰余加群の線形同型を使う。
規約：イデアルは任意。
使われ方：BS Rem 7.15（著者版 p.62）の実 H⁰ への移送。 -/
theorem scalarExtension_faithfullyFlat_of_completelyFaithfullyFlat
    {R : Type u} [CommRing R] (I : Ideal R) (M : ModuleCat.{u} R)
    (hM : IsCompletelyFaithfullyFlat I M) :
    Module.FaithfullyFlat (R ⧸ I)
      ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj M) := by
  let := hM.2
  let e := (quotientScalarExtensionEquiv I M).trans (quotientTensorReductionEquiv I M).symm
  exact Module.FaithfullyFlat.of_linearEquiv _ ((R ⧸ I) ⊗[R] M) e

/-- 概要：mod d の a 完全忠実平坦性から元の二元剰余は忠実平坦。
方針：二重主商の同型に沿う底変換とスカラー拡大の合成同型を使う。
規約：元の加群の正則性・完備性は不要。
使われ方：BS Rem 7.15（著者版 p.62）の導来二元剰余 H⁰ の係数作用。 -/
theorem pairScalarExtension_faithfullyFlat_of_principal_reduction
    {R : Type u} [CommRing R] (a d : R) (M : ModuleCat.{u} R)
    (hred : IsCompletelyFaithfullyFlat
      (Ideal.span {Ideal.Quotient.mk (Ideal.span {d}) a})
      ((ModuleCat.extendScalars (Ideal.Quotient.mk (Ideal.span {d}))).obj M)) :
    Module.FaithfullyFlat (R ⧸ Ideal.span {a, d})
      ((ModuleCat.extendScalars (Ideal.Quotient.mk (Ideal.span {a, d}))).obj M) := by
  let qd := Ideal.Quotient.mk (Ideal.span {d})
  let qa := Ideal.Quotient.mk (Ideal.span {qd a})
  let q := Ideal.Quotient.mk (Ideal.span {a, d})
  have hswap : Ideal.span {d, a} = Ideal.span {a, d} := by rw [Set.pair_comm]
  let eQ := (principalDoubleQuotEquiv d a).trans (Ideal.quotEquivOfEq hswap)
  let k := eQ.toRingHom
  let := k.toAlgebra
  let N := (ModuleCat.extendScalars qa).obj ((ModuleCat.extendScalars qd).obj M)
  have : Module.FaithfullyFlat ((R ⧸ Ideal.span {d}) ⧸ Ideal.span {qd a}) N :=
    scalarExtension_faithfullyFlat_of_completelyFaithfullyFlat _ _ hred
  have hF : Module.FaithfullyFlat (R ⧸ Ideal.span {a, d})
      ((ModuleCat.extendScalars k).obj N) := by
    change Module.FaithfullyFlat (R ⧸ Ideal.span {a, d})
      ((R ⧸ Ideal.span {a, d}) ⊗[(R ⧸ Ideal.span {d}) ⧸ Ideal.span {qd a}] N)
    infer_instance
  have heq : k.comp (qa.comp qd) = q := by
    apply RingHom.ext
    intro r
    change eQ (qa (qd r)) = q r
    change (Ideal.quotEquivOfEq hswap) (principalDoubleQuotEquiv d a (qa (qd r))) = q r
    rw [principalDoubleQuotEquiv_mk, Ideal.quotEquivOfEq_mk]
  let e : (ModuleCat.extendScalars q).obj M ≅ (ModuleCat.extendScalars k).obj N :=
    eqToIso (congrArg (fun g => (ModuleCat.extendScalars g).obj M) heq.symm) ≪≫
      (ModuleCat.extendScalarsComp (qa.comp qd) k).app M ≪≫
      (ModuleCat.extendScalars k).mapIso ((ModuleCat.extendScalarsComp qd qa).app M)
  let := hF
  exact Module.FaithfullyFlat.of_linearEquiv _ ((ModuleCat.extendScalars k).obj N)
    e.toLinearEquiv

end SerrePositivity.BhattScholze.Andre
