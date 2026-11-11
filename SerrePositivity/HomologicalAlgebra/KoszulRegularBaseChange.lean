module

public import SerrePositivity.HomologicalAlgebra.KoszulAlgebraTorComparison
public import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeDiscrete
public import SerrePositivity.HomologicalAlgebra.DerivedQuotientBaseChange
public import SerrePositivity.HomologicalAlgebra.TorAlgebraAcyclicBaseChange
public import SerrePositivity.HomologicalAlgebra.TorSymmetry
public import SerrePositivity.CommutativeAlgebra.Adic.Reduction
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Koszul 正則列の商と導来底変換

## 概要
元の列と像の列が Koszul 分解を与えるとき、その商の導来底変換は通常の商を計算する。

## 方針
既存の Tor と Koszul ホモロジーの比較で高次 Tor を消し、標準 augmentation を使う。

## 規約
Mathlib の通常の導来圏と ModuleCat を用いる。

## 使われ方
BS 著者版 Example 7.9 の自由な初期関係から指定の正則列への移送。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

variable {R C : Type u} [CommRing R] [CommRing C]

/-- 概要：Koszul 分解を保つ列の商は、指定の底変換に対して高次 Tor を持たない。
方針：係数環としての実スカラー加群を識別し、既存の代数係数 Koszul 比較を使う。
規約：両列に Koszul 正則性だけを仮定する。
使われ方：正則列の商の導来底変換を通常の商へ移す。 -/
theorem scalarExtensionTorVanishing_koszul_quotient
    (f : R →+* C) {n : ℕ} (z : Fin n → R)
    (hz : IsKoszulResolution z) (hf : IsKoszulResolution (f ∘ z)) :
    scalarExtensionTorVanishing f (ModuleCat.of R (R ⧸ Ideal.span (Set.range z))) := by
  let := f.toAlgebra
  intro i hi
  let eM := baseChangeScalarAlgebraEquiv (R := R) (B := C)
  let e := ((Tor (ModuleCat R) i).mapIso eM.toModuleIso).app
      (ModuleCat.of R (R ⧸ Ideal.span (Set.range z))) ≪≫
    algebraKoszulTorComparison (C := C) z hz i
  have h : IsZero ((koszulComplex (f ∘ z)).homology (-(i : ℤ))) :=
    hf.isZero _ (by omega)
  exact ((ModuleCat.restrictScalars f).map_isZero h).of_iso e

/-- 概要：二つの Koszul 分解の仮定の下で、商の導来底変換を像の関係の通常商へ同定する。
方針：Tor 消滅により標準 augmentation を同型とし、通常の tensor と商の同型を合成する。
規約：同型は元の底変換の標準 augmentation による。
使われ方：BS 著者版 Example 7.9 の初期関係の除去。 -/
def derivedKoszulQuotientBaseChangeIso
    (f : R →+* C) {n : ℕ} (z : Fin n → R)
    (hz : IsKoszulResolution z) (hf : IsKoszulResolution (f ∘ z)) :
    letI := f.toAlgebra
    (boundedAboveDerivedBaseChange f).obj
      (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R (R ⧸ Ideal.span (Set.range z)))) ≅
    boundedAboveDerivedSingleFunctor.obj
      (ModuleCat.of C (C ⧸ (Ideal.span (Set.range z)).map f)) := by
  let := f.toAlgebra
  let e := (Algebra.TensorProduct.quotIdealMapEquivTensorQuot C
    (Ideal.span (Set.range z))).symm.toLinearEquiv.toModuleIso
  exact boundedAboveDerivedBaseChangeModuleAugmentationIso f _
      (scalarExtensionTorVanishing_koszul_quotient f z hz hf) ≪≫
    boundedAboveDerivedSingleFunctor.mapIso e

/-- 概要：正則列の商への底変換では、像の列が正則なら係数環の高次 Tor が消える。
方針：Koszul 比較で得た Tor の消滅の二変数を交換する。
規約：交換は消滅の判定だけに用い、高次の自然性は要求しない。
使われ方：商を係数環として、その作用を保持する導来底変換。 -/
theorem scalarExtensionTorVanishing_quotient_regular_image
    (f : R →+* C) {n : ℕ} (z : Fin n → R)
    (hz : IsKoszulResolution z) (hf : IsKoszulResolution (f ∘ z)) :
    scalarExtensionTorVanishing (Ideal.Quotient.mk (Ideal.span (Set.range z)))
      (baseChangeScalarModule f) := by
  let J := Ideal.span (Set.range z)
  let q := Ideal.Quotient.mk J
  have hTor := scalarExtensionTorVanishing_koszul_quotient f z hz hf
  intro i hi
  let eQ := baseChangeScalarAlgebraEquiv (R := R) (B := R ⧸ J)
  have h : IsZero (((Tor (ModuleCat R) i).obj (baseChangeScalarModule f)).obj
      (baseChangeScalarModule q)) :=
    (hTor i hi).of_iso (((Tor (ModuleCat R) i).obj (baseChangeScalarModule f)).mapIso
      eQ.toModuleIso)
  let : Subsingleton (TorModule R i (baseChangeScalarModule f) (baseChangeScalarModule q)) :=
    ModuleCat.subsingleton_of_isZero h
  have hs : Subsingleton (TorModule R i (baseChangeScalarModule q) (baseChangeScalarModule f)) :=
    (torComm i (baseChangeScalarModule q) (baseChangeScalarModule f)).injective.subsingleton
  exact ModuleCat.isZero_iff_subsingleton.mpr hs

/-- 概要：Tor 消滅を満たす係数環の導来剰余を、商上の実スカラー加群と同定する。
方針：実スカラー加群の線形同値を既存の導来代数剰余の比較に合成する。
規約：係数環の代数構造を環射として明示する。
使われ方：正則列の商で係数作用を保持する底変換。 -/
def derivedQuotientScalarModuleIso (f : R →+* C) (J : Ideal R)
    (h : scalarExtensionTorVanishing (Ideal.Quotient.mk J) (baseChangeScalarModule f)) :
    let q := Ideal.Quotient.mk J
    let g := Ideal.quotientMap (J.map f) f Ideal.le_comap_map
    (boundedAboveDerivedBaseChange q).obj
      (boundedAboveDerivedSingleFunctor.obj (baseChangeScalarModule f)) ≅
    boundedAboveDerivedSingleFunctor.obj (baseChangeScalarModule g) := by
  let := f.toAlgebra
  let T := R ⧸ J
  let q := Ideal.Quotient.mk J
  let g := Ideal.quotientMap (J.map f) f Ideal.le_comap_map
  let := adicQuotientAlgebra J C
  let eM := baseChangeScalarAlgebraEquiv (R := R) (B := C)
  have hC : scalarExtensionTorVanishing q (ModuleCat.of R C) := by
    intro i hi
    exact (h i hi).of_iso (((Tor (ModuleCat R) i).obj (baseChangeScalarModule q)).mapIso
      eM.symm.toModuleIso)
  let eG := baseChangeScalarAlgebraEquiv (R := T) (B := C ⧸ J.map f)
  exact (boundedAboveDerivedBaseChange q).mapIso
      (boundedAboveDerivedSingleFunctor.mapIso eM.toModuleIso) ≪≫
    derivedQuotientAlgebraIso J C hC ≪≫
    boundedAboveDerivedSingleFunctor.mapIso eG.symm.toModuleIso

/-- 概要：正則列の商への導来底変換を、商環の作用を保って像の通常商に同定する。
方針：標準 augmentation と、実スカラー加群を保つ代数剰余の比較を使う。
規約：得られる同型は元の商環上で線形である。
使われ方：BS 著者版 Example 7.9 の底変換を、残る係数環の上で行う。 -/
def derivedRegularQuotientScalarIso
    (f : R →+* C) {n : ℕ} (z : Fin n → R)
    (hz : IsKoszulResolution z) (hf : IsKoszulResolution (f ∘ z)) :
    let J := Ideal.span (Set.range z)
    let q := Ideal.Quotient.mk J
    let g := Ideal.quotientMap (J.map f) f Ideal.le_comap_map
    (boundedAboveDerivedBaseChange q).obj
      (boundedAboveDerivedSingleFunctor.obj (baseChangeScalarModule f)) ≅
    boundedAboveDerivedSingleFunctor.obj (baseChangeScalarModule g) :=
  derivedQuotientScalarModuleIso f (Ideal.span (Set.range z))
    (scalarExtensionTorVanishing_quotient_regular_image f z hz hf)

end SerrePositivity
