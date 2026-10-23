module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.TwoBoundaryCorrection
public import SerrePositivity.InfinityCategories.F1.KanSquareFiberEquivalence
public import SerrePositivity.InfinityCategories.F1.Cocartesian.FiniteSimplexEquivalence

/-!
概要：同じ二次元境界値を固定した全 native Hom と分類先 Hom の比較同値。
方針：指定 path を保つ補正正方形を、同じ指定境界値の実際の fiber に制限する。
規約：元の全作用と実境界比較の証明済み同値性だけを使う。
使われ方：二次元セルの指定境界値を保った延長空間の降下。
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
variable (j : Fin 2) (p q : CocartesianFibrationCategory (nerve (ULift.{u} (Fin 3))))
local notation "σ" => Iso.hom (stdSimplex.isoNerve 2)
local notation "a" => HornBoundaryOver.apex 1 σ
local notation "N" => cocartesianPullbackNativeLiftCoreFunctor p.val.hom q.val.hom
local notation "P" => cocartesianStrictTransportCoherentDiagram p.val.hom
local notation "Q" => cocartesianStrictTransportCoherentDiagram q.val.hom
local notation "R" => cocartesianPullbackNativeLiftRestriction p.val.hom q.val.hom a
local notation "T" => intervalDiagramGlobalDiagramRestriction P Q a
local notation "V" => cocartesianTwoBoundaryCoherentHomComparison j p q
local notation "U" => cocartesianTwoBoundaryCorrectedHom j p q

local instance twoBoundaryFiberSourceKan (z : Over (nerve (ULift.{u} (Fin 3)))) : KanComplex
    ((N).obj (Opposite.op z)) := cocartesianNativeLiftCoreFunctor_obj_kan p.val.hom q.val.hom z
local instance twoBoundaryFiberTargetKan (z : Over (nerve (ULift.{u} (Fin 3)))) : KanComplex
    ((intervalDiagramLiftOverFunctor P Q).obj (Opposite.op z)) :=
  cocartesianIntervalLiftOverFunctor_obj_kan p q z
local instance twoBoundaryFiberSourceFibration : Fibration R := by
  have : Mono (a).hom :=
    inferInstanceAs (Mono ((boundary 2).ι ≫ (stdSimplex.isoNerve 2).hom))
  exact cocartesianPullbackNativeLiftRestriction_fibration p.val.hom q.val.hom a
local instance twoBoundaryFiberTargetFibration : Fibration T :=
  cocartesianTwoBoundaryTargetRestriction_fibration p q
attribute [local instance] vertexFiber_quasicategory_of_innerFibration

variable (r : ((SSet.uliftFunctor.{u + 1, u}).obj
  ((cocartesianPullbackNativeCoreFunctor p.val.hom q.val.hom).obj
    (Opposite.op a))) _⦋0⦌)

/-- 同じ指定二次元境界値の実際の延長空間の比較。 -/
def cocartesianTwoBoundaryFiberComparison :
    vertexFiber R r ⟶ vertexFiber T ((V).app (Opposite.op ⦋0⦌) r) :=
  kanSquareFiberMap R T U V (cocartesianTwoBoundaryCorrectedHom_comm j p q) r

/-- 同じ fiber 比較は、補正された元の全作用への射影を保持する。 -/
lemma cocartesianTwoBoundaryFiberComparison_ι :
    cocartesianTwoBoundaryFiberComparison j p q r ≫
      vertexFiberι T ((V).app (Opposite.op ⦋0⦌) r) = vertexFiberι R r ≫ U :=
  kanSquareFiberMap_ι R T U V (cocartesianTwoBoundaryCorrectedHom_comm j p q) r

/-- 同じ元の境界値を固定した比較自身は、追加仮定なしに同値。 -/
lemma cocartesianTwoBoundaryFiberComparison_isQCatEquivalence :
    IsQCatEquivalence (cocartesianTwoBoundaryFiberComparison j p q r) :=
  kanSquareFiberMap_isQCatEquivalence R T U V
    (cocartesianTwoBoundaryCorrectedHom_comm j p q) r
    ((cocartesianTwoBoundaryHomCorrection j p q).map_isQCatEquivalence
      (cocartesianStraighteningHomInterval_finite_isQCatEquivalence 2 p q))
    (cocartesianTwoBoundaryCoherentHomComparison_isQCatEquivalence j p q)

end SerrePositivity.InfinityCategories
