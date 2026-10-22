module

public import SerrePositivity.InfinityCategories.F1.CocartesianOneBoundaryLocalCorrection

/-!
概要：同じ一次元境界比較の両端を反変 Hom 図式の値で表示する。
方針：一般の一単体のまま端点表示を揃えてから具体的な面へ適用する。
規約：比較写像と補正正方形を変更しない。
使われ方：高次境界の共有部分の比較を小さい端点表示で扱う。
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

/-- 反変図式の両端表示に揃えた、同じ元の一次元境界比較。 -/
def cocartesianOneBoundaryDiagramComparison :
    (((cocartesianPullbackNativeCoreFunctor p.val.hom q.val.hom) ⋙
      SSet.uliftFunctor.{u + 1, u}).obj (Opposite.op (HornBoundaryOver.apex 0 τ))) ⟶
    (((uliftOverFunctor (nerve C)).op ⋙
      intervalDiagramOverFunctor (cocartesianStrictTransportCoherentDiagram p.val.hom)
        (cocartesianStrictTransportCoherentDiagram q.val.hom)).obj
      (Opposite.op (HornBoundaryOver.apex 0 τ))) :=
  cocartesianOneBoundaryHomComparison j τ p q

/-- 同じ図式表示の比較自身も同値。 -/
lemma cocartesianOneBoundaryDiagramComparison_isQCatEquivalence :
    IsQCatEquivalence (cocartesianOneBoundaryDiagramComparison j τ p q) :=
  cocartesianOneBoundaryHomComparison_isQCatEquivalence j τ p q

/-- 同じ図式表示に揃えた境界比較との厳密な補正正方形。 -/
lemma cocartesianOneBoundaryLocalCorrectedHom_comm_diagram :
    cocartesianOneBoundaryLocalCorrectedHom j τ p q ≫
      cocartesianOneBoundaryLocalTargetRestriction τ p q =
    cocartesianOneBoundaryLocalSourceRestriction τ p q ≫
      cocartesianOneBoundaryDiagramComparison j τ p q :=
  cocartesianOneBoundaryLocalCorrectedHom_comm j τ p q

end SerrePositivity.InfinityCategories
