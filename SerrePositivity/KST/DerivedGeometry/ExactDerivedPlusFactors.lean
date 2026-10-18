module

public import SerrePositivity.KST.DerivedGeometry.ExactDerivedPlus
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived

/-!
概要：bounded below の完全導来関手と複体の局所化の比較。
方針：元の非有界導来化の比較を忠実充満な包含から引き戻す。
規約：実際の複体の像との自然同型を保持する。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の bounded below 導来随伴。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v u' v' w w'
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/--
概要：完全関手の bounded below 導来化は元の複体への適用から局所化で得られる。
方針：非有界導来化の比較を bounded below の忠実充満な包含で引き戻す。
規約：比較は自然同型であり、対象ごとの同型だけではない。
使われ方：TT §3、Toën §3.2 の導来随伴の左側。
-/
def exactDerivedFunctorPlusFactors :
    DerivedCategory.Plus.Q ⋙ exactDerivedFunctorPlus F ≅
      F.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q := by
  apply ((DerivedCategory.TStructure.t.plus.fullyFaithfulι).whiskeringRight _).preimageIso
  exact Functor.isoWhiskerLeft (CochainComplex.Plus.ι C) F.mapDerivedCategoryFactors

/--
概要：bounded below への完全導来化は複体からの左導来関手である。
方針：局所化との自然同型を、準同型を反転する関手の導来関手の普遍性へ適用する。
規約：存在を未証明フィールドにしない。
使われ方：TT §3・§8、Toën §3.2 の bounded below 導来随伴。
-/
instance exactDerivedFunctorPlus_isLeftDerivedFunctor :
    (exactDerivedFunctorPlus F).IsLeftDerivedFunctor (exactDerivedFunctorPlusFactors F).hom
      (CochainComplex.Plus.quasiIso C) :=
  Functor.isLeftDerivedFunctor_of_inverts (CochainComplex.Plus.quasiIso C) _
    (exactDerivedFunctorPlusFactors F)

end SerrePositivity.KST.DerivedGeometry
