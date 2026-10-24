module

public import SerrePositivity.InfinityCategories.F2.Presentable.CoproductFromFiniteSubsets
public import SerrePositivity.InfinityCategories.F2.Presentable.ColimitFromDiscreteRestrictions
public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaFiniteCoproductExistence
public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaGeometricRealizations

/-!
概要：P_Σ 内の表現可能図式の全小余極限。
方針：有限余積から小余積を構成し、離散制限と幾何学的実現で組み立てる。
規約：P_Σ 全体の余完備性も一般局所化も仮定しない。
使われ方：全前層圏から P_Σ への専用反映の局所存在入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits
variable {C : SSet.{u}} [Quasicategory C]
    (hC : ∀ (J : Type u) [Finite J] (p : nerve (Discrete J) ⟶ C.op), HasLimit p)
include hC

/-- 概要：表現可能対象の元の小離散図式は P_Σ 内で余積を持つ。
方針：有限制限に Yoneda の有限余積保存を使い、filtered に組み立てる。
規約：元の小さい底の離散図式を保持する。
使われ方：専用反映の bar 各次数の余積。 -/
lemma sigmaYoneda_smallDiscreteDiagram_hasColimit {I : Type u}
    (p : nerve (Discrete I) ⟶ C) :
    HasColimit ((SSet.uliftFunctor.{u + 1, u}).map p ≫ sigmaYonedaInfinityMap C) := by
  apply hasColimit_discrete_of_finiteRestrictions (sigma_hasSmallSiftedColimits C)
  intro J hJ f
  simpa only [Functor.map_comp, Category.assoc] using
    sigmaYoneda_finiteDiagram_hasColimit hC (f ≫ p)

/-- 概要：元の小さい底の全図式の Yoneda 像は P_Σ 内で余極限を持つ。
方針：全離散制限の小余積を作り、bar 図式の幾何学的実現で合成する。
規約：元の任意の小さい形状と全高次の射を保持する。
使われ方：前層の elements 図式に適用する専用反映の構成。 -/
lemma sigmaYoneda_smallDiagram_hasColimit {K : SSet.{u}} (p : K ⟶ C) :
    HasColimit ((SSet.uliftFunctor.{u + 1, u}).map p ≫ sigmaYonedaInfinityMap C) := by
  apply hasColimit_of_discreteRestrictions_geometricRealizations
    _ _ (sigma_hasSmallGeometricRealizations C)
  intro I f
  simpa only [Functor.map_comp, Category.assoc] using
    sigmaYoneda_smallDiscreteDiagram_hasColimit hC (f ≫ p)

end SerrePositivity.InfinityCategories.F2.Presentable
