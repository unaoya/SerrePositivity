module

public import SerrePositivity.KST.DerivedGeometry.ExactDerivedPlusFactors
public import SerrePositivity.KST.DerivedGeometry.InjectiveResolutionPlusModel

/-!
概要：完全関手の bounded below 導来化は単一複体と可換。
方針：導来局所化との比較と項別関手の単一複体比較を合成する。
規約：全ての整数次数で同じ完全関手を使う。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 のアフィン導来余単位。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/--
概要：完全関手の導来化の単一対象の像は元の関手の値の単一対象と同型。
方針：項別関手の単一複体比較を元の導来局所化へ写す。
規約：元の導来化の比較射を保持する。
使われ方：TT §3、Toën §3.2 の準連接層が導来 tilde の像に属すこと。
-/
def exactDerivedPlusSingleIso (n : ℤ) (X : C) :
    (exactDerivedFunctorPlus F).obj ((DerivedCategory.Plus.singleFunctor C n).obj X) ≅
      (DerivedCategory.Plus.singleFunctor D n).obj (F.obj X) := by
  let e : F.mapCochainComplexPlus.obj ((singleComplexPlus n).obj X) ≅
      (singleComplexPlus n).obj (F.obj X) :=
    ObjectProperty.isoMk (CochainComplex.plus D)
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) n).app X)
  exact (exactDerivedFunctorPlusFactors F).app ((singleComplexPlus n).obj X) ≪≫
    DerivedCategory.Plus.Q.mapIso e

end SerrePositivity.KST.DerivedGeometry
