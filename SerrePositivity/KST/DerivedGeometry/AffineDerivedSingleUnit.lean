module

public import SerrePositivity.KST.DerivedGeometry.AffineDerivedPlusAdjunction
public import SerrePositivity.KST.DerivedGeometry.RightDerivedPlusSingleComparison
public import SerrePositivity.KST.DerivedGeometry.DerivedPlusUnit

/-!
概要：アフィン係数の bounded below 導来随伴の単位は単一加群上で同型。
方針：準連接層の非輪状性を実際の右導来比較に適用し、導来単位の因子化を使う。
規約：元の全係数加群層圏で分解し、H の平坦性・可換性を仮定しない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 のアフィン完全忠実性の第一段階。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits AlgebraicGeometry
namespace SerrePositivity.KST.DerivedGeometry
variable {R : CommRingCat.{u}} (H : Type u) [Ring H] [Algebra R H]
  [HasDerivedCategory (ModuleCat.{u} H)]
  [HasDerivedCategory (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).Modules]

/--
概要：準連接係数層の単一複体上で実際の右導来比較は同型。
方針：全ての通常の高次大域切断の消滅を一般の比較定理へ適用する。
規約：準連接層の圏での分解へ置換しない。
使われ方：TT §3、Toën §3.2 の係数 tilde の非輪状性。
-/
lemma affineΓPlusUnit_single_isIso
    (F : (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).QCoh) :
    IsIso ((affineCoefficientΓ (R := R) H).rightDerivedFunctorPlusUnit.app
      ((singleComplexPlus 0).obj F.obj)) :=
  rightDerivedPlusUnit_single_isIso (affineCoefficientΓ (R := R) H) F.obj
    (affineCoefficientΓ_rightDerived_isZero H F)

/--
概要：単一加群へ tilde を項別に適用した複体上で右導来比較は同型。
方針：項別 tilde と単一複体との比較同型を使い、準連接層の結果を移す。
規約：実際の複体上の比較写像に対する結論。
使われ方：TT §3・§8、Toën §3.2 の導来単位の因子化。
-/
lemma affineΓPlusUnit_tilde_single_isIso (M : ModuleCat.{u} H) :
    IsIso ((affineCoefficientΓ (R := R) H).rightDerivedFunctorPlusUnit.app
      ((affineCoefficientTildeFunctor (R := R) H).mapCochainComplexPlus.obj
        ((singleComplexPlus 0).obj M))) := by
  let e : (affineCoefficientTildeFunctor (R := R) H).mapCochainComplexPlus.obj
      ((singleComplexPlus 0).obj M) ≅
        (singleComplexPlus 0).obj ((affineCoefficientTildeFunctor (R := R) H).obj M) :=
    ObjectProperty.isoMk (CochainComplex.plus _)
      ((HomologicalComplex.singleMapHomologicalComplex
        (affineCoefficientTildeFunctor (R := R) H) (.up ℤ) 0).app M)
  exact (NatTrans.isIso_app_iff_of_iso
    (affineCoefficientΓ (R := R) H).rightDerivedFunctorPlusUnit e).mpr
      (affineΓPlusUnit_single_isIso H ((affineCoefficientEquivalence (R := R) H).inverse.obj M))

/--
概要：bounded below アフィン導来随伴の単位は次数零の単一加群で同型。
方針：通常のアフィン単位の同型性と tilde 単一複体上の右導来比較を因子化公式に代入する。
規約：一般の非有界対象での同型性は別の主張。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の bounded below アフィン比較。
-/
lemma affineDerivedPlus_unit_single_isIso (M : ModuleCat.{u} H) :
    IsIso ((affineDerivedPlusAdjunction (R := R) H).unit.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj M)) := by
  have := affineΓPlusUnit_tilde_single_isIso (R := R) H M
  exact derivedPlusAdjunction_unit_isIso_Q (affineCoefficientTildeAdjunction (R := R) H)
    ((singleComplexPlus 0).obj M)

end SerrePositivity.KST.DerivedGeometry
