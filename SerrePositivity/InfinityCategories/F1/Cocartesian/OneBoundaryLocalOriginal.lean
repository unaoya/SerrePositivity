module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.OneBoundaryDiagramComparison
public import SerrePositivity.InfinityCategories.F1.Cocartesian.StandardSimplexOriginal

/-!
概要：一単体の境界と厳密に可換な同じ補正比較を、元の大域 Hom 作用へ戻す。
方針：同じ補正同型を大域制限で前合成し、既存の標準セルの指定同型へ続ける。
規約：元の分類主写像と一単体上の全局所比較を保持する。
使われ方：高次境界の面側の大域同型と、その共有境界での指定像。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {C : Type u} [Category.{u} C] (j : Fin 2)
  (τ : (Δ[1] : SSet.{u}) ⟶ nerve C) (p q : CocartesianFibrationCategory (nerve C))

/-- 同じ補正一単体比較は、元の大域の全 Hom 作用の制限と指定同型で一致する。 -/
def cocartesianOneBoundaryLocalCorrectedHom_originalIso :
    FunctorIso
      (cocartesianPullbackNativeLiftRestriction p.val.hom q.val.hom (Over.mk τ) ≫
        cocartesianOneBoundaryLocalCorrectedHom j τ p q)
      (cocartesianStraighteningHomInterval p q ≫ intervalDiagramRestriction
        ((SSet.uliftFunctor.{u + 1, u}).map τ)
        (cocartesianStrictTransportCoherentDiagram p.val.hom)
        (cocartesianStrictTransportCoherentDiagram q.val.hom)) :=
  (cocartesianOneBoundaryLocalCorrectedHomIso j τ p q).precomp
    (cocartesianPullbackNativeLiftRestriction p.val.hom q.val.hom (Over.mk τ)) ≪≫
      cocartesianStandardSimplexHomComparison_originalIso τ p q

end SerrePositivity.InfinityCategories
