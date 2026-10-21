module

public import SerrePositivity.InfinityCategories.F1.CocartesianOneBoundaryFiberComparison
public import SerrePositivity.InfinityCategories.F1.CocartesianFiniteSimplexEquivalence

/-!
概要：有限区間上の元の両端固定 Hom の同じ比較の同値性。
方針：元の全 Hom 作用と実際の一次元境界比較の同値を同じ fiber へ移す。
規約：追加の充満忠実性・同値性の仮定を置かない。
使われ方：セル境界の比較を高次へ帰納する初期値。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable (i : Fin 2)
  (p q : CocartesianFibrationCategory (nerve (ULift.{u} (Fin 2))))
local notation "σ" => Iso.hom (stdSimplex.isoNerve 1)
local notation "R" => cocartesianPullbackNativeLiftRestriction p.val.hom q.val.hom
  (HornBoundaryOver.apex 0 σ)

local instance : Fibration R := by
  have : Mono (HornBoundaryOver.apex 0 σ).hom :=
    inferInstanceAs (Mono ((boundary 1).ι ≫ (stdSimplex.isoNerve 1).hom))
  exact cocartesianPullbackNativeLiftRestriction_fibration p.val.hom q.val.hom
    (HornBoundaryOver.apex 0 σ)
local instance : Fibration (cocartesianOneBoundaryTargetRestriction σ p q) :=
  cocartesianOneBoundaryTargetRestriction_fibration σ p q
attribute [local instance] vertexFiber_quasicategory_of_innerFibration

/-- 元の区間上の全相対 Hom の core の両端を固定した、同じ比較自体の同値性。 -/
lemma cocartesianIntervalBoundaryFiberComparison_isQCatEquivalence
    (r : ((SSet.uliftFunctor.{u + 1, u}).obj
      ((cocartesianPullbackNativeCoreFunctor p.val.hom q.val.hom).obj
        (Opposite.op (HornBoundaryOver.apex 0 (stdSimplex.isoNerve 1).hom)))) _⦋0⦌) :
    IsQCatEquivalence (cocartesianOneBoundaryFiberComparison i
      (stdSimplex.isoNerve 1).hom p q r) :=
  cocartesianOneBoundaryFiberComparison_isQCatEquivalence i _ p q r
    (cocartesianStraighteningHomInterval_finite_isQCatEquivalence 1 p q)

end SerrePositivity.InfinityCategories
