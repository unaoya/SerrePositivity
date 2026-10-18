module

public import SerrePositivity.KST.DerivedGeometry.ComplexAdjunction
public import SerrePositivity.KST.DerivedGeometry.DerivedPlusPostcomp

/-!
概要：完全左随伴と加法的右随伴から bounded below 導来随伴を構成する。
方針：複体上の実際の随伴と、後合成でも保たれる左・右導来の普遍性を使う。
規約：導来随伴の存在を仮定として要求しない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の係数アフィン導来比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives D]
  {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/--
概要：完全左随伴と加法的右随伴は bounded below 導来圏上の随伴を誘導する。
方針：左導来の比較同型、injective 模型による右導来の普遍性、複体上の随伴を用いる。
規約：右随伴の完全性は要求しない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の実際の係数導来随伴。
-/
def derivedPlusAdjunction (adj : F ⊣ G) :
    exactDerivedFunctorPlus F ⊣ G.rightDerivedFunctorPlus := by
  have := exactDerivedPlus_postcomp_isLeftDerivedFunctor F G.rightDerivedFunctorPlus
  have := rightDerivedPlus_postcomp_isRightDerivedFunctor G (exactDerivedFunctorPlus F)
  exact (adjunctionComplexPlus adj).derived (CochainComplex.Plus.quasiIso C)
    (CochainComplex.Plus.quasiIso D) (exactDerivedFunctorPlusFactors F).hom
      G.rightDerivedFunctorPlusUnit

end SerrePositivity.KST.DerivedGeometry
