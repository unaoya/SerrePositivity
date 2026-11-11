module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedAlgebraH0
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalClassicalComparison

/-!
# 同じ座標の二元完備化

## 概要
(a,a) 完備化の実際の零次環を a 完備化に同定し、正則性を移す。

## 方針
二つの環の普遍性から標準単位を保つ互いに逆の代数射を作る。

## 規約
完備化の前の環の完備性は仮定しない。

## 使われ方
BS 著者版 Construction 6.1 の (p,p) 完備化した結晶被覆。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

namespace SerrePositivity.DerivedCompletion

open CategoryTheory

variable (R : Type u) [CommRing R] (a : R)

/-- 概要：同じ座標の二元完備化は主元完備化と標準的に同型。
方針：両方の普遍性により係数上の恒等射を延長する。
規約：実際の零次環と標準代数構造を使う。
使われ方：BS 著者版 Construction 6.1 の結晶被覆の正則性。 -/
@[expose] def pairCompletionRepeatedAlgEquiv :
    letI := pairCompletionCommRing R a a
    letI := pairCompletionAlgebra R a a
    letI := principalCompletionCommRing R a
    letI := principalCompletionAlgebra R a
    PairCompletionH0 R a a ≃ₐ[R] PrincipalCompletionH0 R a := by
  letI := pairCompletionCommRing R a a
  letI := pairCompletionAlgebra R a a
  letI := principalCompletionCommRing R a
  letI := principalCompletionAlgebra R a
  let f := pairCompletionLiftAlgHom R a a (PrincipalCompletionH0 R a)
    (principalCompletionH0_isModuleComplete R a) (principalCompletionH0_isModuleComplete R a)
  let g := principalCompletionToPair R a a
  have hfg : f.comp g = AlgHom.id R _ :=
    (principalCompletion_existsUnique_algHom R a (PrincipalCompletionH0 R a)
      (principalCompletionH0_isModuleComplete R a)).unique trivial trivial
  have hgf : g.comp f = AlgHom.id R _ :=
    (pairCompletion_existsUnique_algHom R a a (PairCompletionH0 R a a)
      (pairCompletionH0_isModuleComplete_first R a a)
      (pairCompletionH0_isModuleComplete_second R a a)).unique trivial trivial
  exact AlgEquiv.ofAlgHom f g hfg hgf

/-- 概要：繰り返した座標の比較は標準単位を保つ。
方針：比較が係数環上の代数同型であることを使う。
規約：任意の係数の元を追跡する。
使われ方：BS 著者版 Construction 6.1 の生成元の照合。 -/
theorem pairCompletionRepeatedAlgEquiv_unit (x : R) :
    let := pairCompletionCommRing R a a
    let := pairCompletionAlgebra R a a
    let := principalCompletionCommRing R a
    let := principalCompletionAlgebra R a
    pairCompletionRepeatedAlgEquiv R a (pairCompletionUnitRingHom R a a x) =
      principalCompletionUnitRingHom R a x := by
  let := pairCompletionCommRing R a a
  let := pairCompletionAlgebra R a a
  let := principalCompletionCommRing R a
  let := principalCompletionAlgebra R a
  exact (pairCompletionRepeatedAlgEquiv R a).commutes x

/-- 概要：元が正則なら同じ二座標の完備化でもその標準像は正則。
方針：主元完備化での正則性を標準単位を保つ同型で移す。
規約：完備化前の元の正則性だけを仮定する。
使われ方：BS 著者版 Construction 6.1 の結晶被覆の p 正則性。 -/
theorem pairCompletionRepeated_regular (ha : IsSMulRegular R a) :
    let := pairCompletionCommRing R a a
    IsSMulRegular (PairCompletionH0 R a a) (pairCompletionUnitRingHom R a a a) := by
  let := pairCompletionCommRing R a a
  let := pairCompletionAlgebra R a a
  let := principalCompletionCommRing R a
  let := principalCompletionAlgebra R a
  let e := pairCompletionRepeatedAlgEquiv R a
  have h := principalCompletionH0_smul_injective_of_regular R a ha
  change Function.Injective (fun x : PairCompletionH0 R a a =>
    pairCompletionUnitRingHom R a a a * x)
  intro x y hxy
  apply e.injective
  apply h
  have hm : principalCompletionUnitRingHom R a a * e x =
      principalCompletionUnitRingHom R a a * e y := by
    have he : e (pairCompletionUnitRingHom R a a a) = principalCompletionUnitRingHom R a a :=
      pairCompletionRepeatedAlgEquiv_unit R a a
    simpa only [map_mul, he] using congrArg e hxy
  exact ((principalCompletionH0_isCompleteModuleReflection R a).mul_scalar_unit a (e x)).symm.trans
    (hm.trans ((principalCompletionH0_isCompleteModuleReflection R a).mul_scalar_unit a (e y)))

end SerrePositivity.DerivedCompletion
