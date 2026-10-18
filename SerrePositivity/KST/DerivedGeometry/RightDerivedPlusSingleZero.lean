module

public import SerrePositivity.KST.DerivedGeometry.RightDerivedPlusSingle
public import SerrePositivity.KST.DerivedGeometry.LeftExactLowestHomology
public import Mathlib.Algebra.Homology.SingleHomology

/-!
概要：左完全関手の bounded below 右導来の単一対象上の零次数は元の関手の値と同型。
方針：同じ injective 分解で計算し、最下次数の核の保存と分解の準同型性を使う。
規約：正次数の消滅はここでは要求しない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 のアフィン導来比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
  {X : C} (I : InjectiveResolution X)

/--
概要：左完全関手の右導来の単一対象の零次数は元の関手の値と同型。
方針：injective 模型、導来局所化のコホモロジー、核の保存、分解の準同型を順に比較する。
規約：元の全層圏の分解に適用できる。
使われ方：TT §3・§8、Toën §3.2 のアフィンの零次数比較。
-/
def rightDerivedPlusSingleZeroIso :
    (DerivedCategory.Plus.homologyFunctor D 0).obj
      (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj X)) ≅
      F.obj X :=
  (DerivedCategory.Plus.homologyFunctor D 0).mapIso (rightDerivedPlusSingleIso F I) ≪≫
    (DerivedCategory.homologyFunctorFactors D 0).app
      ((F.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex) ≪≫
    leftExactHomologyZeroIso F I.cochainComplex ≪≫
    F.mapIso (asIso (HomologicalComplex.homologyMap I.ι' 0)).symm ≪≫
    F.mapIso ((HomologicalComplex.homologyFunctorSingleIso C (.up ℤ) 0).app X)

end SerrePositivity.KST.DerivedGeometry
