module

public import SerrePositivity.KST.DerivedGeometry.DerivedPlusAdjunction

/-!
概要：bounded below 導来随伴の単位と元の複体随伴の単位の比較。
方針：実際の左導来持ち上げの因子化公式を使う。
規約：右導来比較の同型性は別に検証して適用する。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 のアフィン導来単位。
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
  [PreservesFiniteLimits F] [PreservesFiniteColimits F] (adj : F ⊣ G)

/--
概要：元の随伴の単位が同型なら複体随伴の単位も同型。
方針：鎖写像の各成分は元の単位であることを Hom 同値から計算する。
規約：局所化前の複体の圏での主張。
使われ方：TT §3、Toën §3.2 の通常のアフィン単位の移送。
-/
lemma adjunctionComplexPlus_unit_isIso [IsIso adj.unit] (K : CochainComplex.Plus C) :
    IsIso ((adjunctionComplexPlus adj).unit.app K) := by
  have (i : ℤ) : IsIso (((CochainComplex.Plus.ι C).map
      ((adjunctionComplexPlus adj).unit.app K)).f i) := by
    change IsIso ((adj.homEquiv _ _) (𝟙 _))
    rw [adj.homEquiv_id]
    infer_instance
  have : IsIso ((CochainComplex.Plus.ι C).map
      ((adjunctionComplexPlus adj).unit.app K)) :=
    HomologicalComplex.Hom.isIso_of_components _
  exact isIso_of_fully_faithful (CochainComplex.Plus.ι C) _

/--
概要：導来単位は局所化後の複体単位と右導来比較に因子化する。
方針：Mathlib の導来随伴の単位の因子化公式を実際の関手へ特殊化する。
規約：左右導来比較は元の構成のもの。
使われ方：TT §3・§8、Toën §3.2 の導来単位の同型判定。
-/
lemma derivedPlusAdjunction_unit_fac (K : CochainComplex.Plus C) :
    (derivedPlusAdjunction adj).unit.app (DerivedCategory.Plus.Q.obj K) ≫
      G.rightDerivedFunctorPlus.map ((exactDerivedFunctorPlusFactors F).hom.app K) =
    DerivedCategory.Plus.Q.map ((adjunctionComplexPlus adj).unit.app K) ≫
      G.rightDerivedFunctorPlusUnit.app (F.mapCochainComplexPlus.obj K) := by
  have := exactDerivedPlus_postcomp_isLeftDerivedFunctor F G.rightDerivedFunctorPlus
  have := rightDerivedPlus_postcomp_isRightDerivedFunctor G (exactDerivedFunctorPlus F)
  exact (adjunctionComplexPlus adj).derivedη_fac_app
    (CochainComplex.Plus.quasiIso C) (exactDerivedFunctorPlusFactors F).hom
      G.rightDerivedFunctorPlusUnit K

/--
概要：元の単位と右導来比較が同型の複体では導来単位も同型。
方針：単位の因子化の両側を同型で挟んで判定する。
規約：比較写像の同型性を検証した対象ごとに適用する。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の単一対象のアフィン単位。
-/
lemma derivedPlusAdjunction_unit_isIso_Q [IsIso adj.unit] (K : CochainComplex.Plus C)
    [IsIso (G.rightDerivedFunctorPlusUnit.app (F.mapCochainComplexPlus.obj K))] :
    IsIso ((derivedPlusAdjunction adj).unit.app (DerivedCategory.Plus.Q.obj K)) := by
  have : IsIso ((adjunctionComplexPlus adj).unit.app K) := adjunctionComplexPlus_unit_isIso adj K
  have : IsIso ((derivedPlusAdjunction adj).unit.app (DerivedCategory.Plus.Q.obj K) ≫
      G.rightDerivedFunctorPlus.map ((exactDerivedFunctorPlusFactors F).hom.app K)) := by
    rw [derivedPlusAdjunction_unit_fac adj K]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (G.rightDerivedFunctorPlus.map ((exactDerivedFunctorPlusFactors F).hom.app K))

end SerrePositivity.KST.DerivedGeometry
