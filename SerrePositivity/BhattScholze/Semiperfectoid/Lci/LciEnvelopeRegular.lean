module

public import SerrePositivity.BhattScholze.Andre.Envelope.RootSource
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.DerivedPurity

/-!
# lci 包絡候補の生成元の正則性

## 概要
通常の押し出しの完備化環で、生成元の正則性を同じ逐次完備化の Koszul 剰余から判定する。

## 方針
スカラー錐の次数 −1 の消滅から零次ホモロジーでの単射性を得る。
標準単位を保つ線形比較で実際の完備化環へ移す。

## 規約
BS 著者版 Example 7.9 の通常の環候補を用いる。

## 使われ方
正則列に対する分母の正則性を剰余計算へ帰着する。
-/

public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

namespace SerrePositivity.BhattScholze

open CategoryTheory CategoryTheory.Limits DerivedCompletion

attribute [local instance] HasDerivedCategory.standard

/-- 概要：逐次完備化の d 錐の負一次消滅は、環候補での d の正則性を与える。
方針：錐のホモロジー列で d の作用の単射性を得て、既存の線形比較を使う。
規約：BS 著者版 Example 7.9 の通常の押し出し環に適用する。
使われ方：剰余の離散性から完備化に prism 構造を付ける。 -/
theorem pdCompletion_generator_regular_of_scalarCone_homology_isZero
    (N : Type u) [CommRing N] (p : ℕ) (d : N)
    (h : IsZero ((DerivedCategory.homologyFunctor (ModuleCat N) (-1)).obj
      ((derivedScalarConeFunctor N d).obj (IteratedPDCompletionObject N (p : N) d)))) :
    let := pdCompletionCommRing N p d
    IsRegular (pdCompletionUnit N p d d) := by
  let := pdCompletionCommRing N p d
  let := pdCompletionAlgebra N p d
  let e := iteratedPDH0LinearEquiv N (p : N) d p rfl
  have hZ := derived_homology_smul_injective_of_scalarCone_isZero d
    (IteratedPDCompletionObject N (p : N) d) 0 (by simpa using h)
  have hM : Function.Injective (fun x : PDCompletionH0 N p d => d • x) := by
    intro x y hxy
    apply e.symm.injective
    apply hZ
    simpa only [← e.symm.map_smul] using congrArg e.symm hxy
  have hd : algebraMap N (PDCompletionH0 N p d) d = pdCompletionUnit N p d d :=
    pairCompletion_algebraMap N (p : N) d d
  have hl : Function.Injective (fun x : PDCompletionH0 N p d =>
      pdCompletionUnit N p d d * x) := by
    simpa only [Algebra.smul_def, hd] using hM
  exact ⟨hl, fun x y hxy => hl (by simpa only [mul_comm] using hxy)⟩

/-- 概要：通常の押し出しの d 錐を p 完備化した後の負一次消滅で正則性を判定できる。
方針：p 完備化とスカラー錐を交換し、d 完備化の単位で d 錐を同定する。
規約：BS 著者版 Example 7.9。押し出し環そのものにおける d の正則性は仮定しない。
使われ方：通常のテンソル環から作る包絡の正則性判定。 -/
theorem pdCompletion_generator_regular_of_completed_scalarCone_homology_isZero
    (N : Type u) [CommRing N] (p : ℕ) (d : N)
    (h : IsZero ((DerivedCategory.homologyFunctor (ModuleCat N) (-1)).obj
      ((derivedComplexCompletionFunctor N (p : N)).obj
        ((derivedScalarConeFunctor N d).obj
          ((DerivedCategory.singleFunctor (ModuleCat N) 0).obj (ModuleCat.of N N)))))) :
    let := pdCompletionCommRing N p d
    IsRegular (pdCompletionUnit N p d d) := by
  let X := boundedAboveDerivedSingleFunctor.obj (ModuleCat.of N N)
  let Y := (boundedAboveDerivedCompletionFunctor N (p : N)).obj X
  let η := (derivedComplexCompletionUnit N d).app Y.obj
  have hη : IsIso ((derivedScalarConeFunctor N d).map η) := by
    have hη₁ := derivedScalarCone_map_isIso_of_completion N d η
      (derivedComplexCompletionFunctor_map_unit_isIso N d Y.obj) 1
    exact Eq.mp (congrArg (fun z : N => IsIso ((derivedScalarConeFunctor N z).map η))
      (_root_.pow_one d)) hη₁
  let e := completionScalarConeIso N (p : N) d X ≪≫
    @asIso _ _ _ _ ((derivedScalarConeFunctor N d).map η) hη
  exact pdCompletion_generator_regular_of_scalarCone_homology_isZero N p d
    (h.of_iso ((DerivedCategory.homologyFunctor (ModuleCat N) (-1)).mapIso e.symm))

end SerrePositivity.BhattScholze
