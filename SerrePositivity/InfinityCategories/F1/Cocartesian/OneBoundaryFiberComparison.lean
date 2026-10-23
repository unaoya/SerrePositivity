module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.OneBoundaryCorrection
public import SerrePositivity.InfinityCategories.F1.KanSquareFiberEquivalence

/-!
概要：同じ一次元境界値を固定した元の native Hom と分類先 Hom の比較。
方針：指定 path で補正した正方形を、同じ指定値の実際の fiber へ制限する。
規約：全空間の同値性は明示的な証明としてのみ受け取り、instance 仮定にしない。
使われ方：有限区間の両端固定 Hom の同値性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {C : Type u} [Category.{u} C] (i : Fin 2)
  (σ : (Δ[1] : SSet.{u}) ⟶ nerve C) [Mono σ]
  (p q : CocartesianFibrationCategory (nerve C))
local notation "R" => cocartesianPullbackNativeLiftRestriction p.val.hom q.val.hom
  (HornBoundaryOver.apex 0 σ)
local notation "T" => cocartesianOneBoundaryTargetRestriction σ p q
local notation "V" => cocartesianOneBoundaryHomComparison i σ p q
local notation "U" => cocartesianOneBoundaryCorrectedHom i σ p q

local instance {D : SSet.{u}} (a : D ⟶ nerve C) : InnerFibration (pullback.fst a q.val.hom) :=
  ⟨innerFibrations.pullback_fst a q.val.hom (InnerFibration.mem (q := q.val.hom))⟩
local instance (z : Over (nerve C)) : KanComplex ((SSet.uliftFunctor.{u + 1, u}).obj
    ((cocartesianPullbackNativeCoreFunctor p.val.hom q.val.hom).obj (Opposite.op z))) :=
  inferInstanceAs (KanComplex ((SSet.uliftFunctor.{u + 1, u}).obj (quasicategoryCore
    (cocartesianRelativeFunctorSpace (pullback.fst z.hom p.val.hom)
      (pullback.fst z.hom q.val.hom)) : SSet.{u})))

local instance : Fibration R := by
  have : Mono (HornBoundaryOver.apex 0 σ).hom :=
    inferInstanceAs (Mono ((boundary 1).ι ≫ σ))
  exact cocartesianPullbackNativeLiftRestriction_fibration p.val.hom q.val.hom
    (HornBoundaryOver.apex 0 σ)
local instance : Fibration T := cocartesianOneBoundaryTargetRestriction_fibration σ p q
attribute [local instance] vertexFiber_quasicategory_of_innerFibration

variable (r : ((SSet.uliftFunctor.{u + 1, u}).obj
  ((cocartesianPullbackNativeCoreFunctor p.val.hom q.val.hom).obj
    (Opposite.op (HornBoundaryOver.apex 0 σ)))) _⦋0⦌)

/-- 同じ両端値を指定した、元の実際の延長空間の比較。 -/
def cocartesianOneBoundaryFiberComparison :
    vertexFiber R r ⟶ vertexFiber T ((V).app (Opposite.op ⦋0⦌) r) :=
  kanSquareFiberMap R T U V (cocartesianOneBoundaryCorrectedHom_comm i σ p q) r

/-- 同じ比較は補正した全空間の作用への射影を保持する。 -/
lemma cocartesianOneBoundaryFiberComparison_ι :
    cocartesianOneBoundaryFiberComparison i σ p q r ≫
      vertexFiberι T ((V).app (Opposite.op ⦋0⦌) r) = vertexFiberι R r ≫ U :=
  kanSquareFiberMap_ι R T U V (cocartesianOneBoundaryCorrectedHom_comm i σ p q) r

/-- 元の全作用が同値なら、この同じ両端固定の比較自身も同値。 -/
lemma cocartesianOneBoundaryFiberComparison_isQCatEquivalence
    (hS : IsQCatEquivalence (cocartesianStraighteningHomInterval p q)) :
    IsQCatEquivalence (cocartesianOneBoundaryFiberComparison i σ p q r) := by
  exact kanSquareFiberMap_isQCatEquivalence R T U V
    (cocartesianOneBoundaryCorrectedHom_comm i σ p q) r
    ((cocartesianOneBoundaryHomCorrection i σ p q).map_isQCatEquivalence hS)
    (cocartesianOneBoundaryHomComparison_isQCatEquivalence i σ p q)

end SerrePositivity.InfinityCategories
