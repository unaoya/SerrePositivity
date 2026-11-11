module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ScaffoldPullbackNativeLift
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.KanSquareFiberEquivalence

/-!
概要：セル貼合せと同じ宇宙で、元の native 境界固定 Hom を同じ scaffold と比較する。
方針：宇宙を揃えた同じ自然な正方形を、元の指定境界値の fiber に制限する。
規約：任意の単射な境界を許し、元の全相対 Hom の指定値を保つ。
使われ方：セル付加の native 延長空間からの同じ局所比較。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration
variable {C : Type u} [Category.{u} C] {E F : SSet.{u}}
  (p : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] (q : F ⟶ nerve C)
  [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration q] {a b : Over (nerve C)} (f : a ⟶ b)
  (r : ((SSet.uliftFunctor.{u + 1, u}).obj
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeCoreFunctor p q).obj (Opposite.op a))) _⦋0⦌)

local instance (z : Over (nerve C)) : InnerFibration (pullback.fst z.hom q) :=
  ⟨innerFibrations.pullback_fst z.hom q (InnerFibration.mem (q := q))⟩

local instance (z : Over (nerve C)) :
    Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldPullbackMarkedHom p q z) :=
  inferInstanceAs (Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorSpace q _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldPullbackMark p z)))

local instance (z : Over (nerve C)) : KanComplex
    ((SSet.uliftFunctor.{u + 1, u}).obj
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeCoreFunctor p q).obj (Opposite.op z))) :=
  inferInstanceAs (KanComplex ((SSet.uliftFunctor.{u + 1, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.cocartesianRelativeFunctorSpace (pullback.fst z.hom p) (pullback.fst z.hom q)) : SSet.{u})))

local instance [Mono f.left] : Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeLiftPre p q f) := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.core_cocartesianPullbackNativePre_fibration p q f
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.fibration_uliftFunctor_map _

local instance [Mono f.left] :
    Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ScaffoldPullbackNativeLift.cocartesianScaffoldPullbackMarkedLiftRestriction p q f) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ScaffoldPullbackNativeLift.cocartesianScaffoldPullbackMarkedLiftRestriction_fibration p q f

/-- 元の大きい宇宙の native Hom の指定値の fiber からの同じ scaffold 比較。 -/
def cocartesianScaffoldNativeLiftBoundaryPre :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.kanSquareFiberMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeLiftPre p q f)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ScaffoldPullbackNativeLift.cocartesianScaffoldPullbackMarkedLiftRestriction p q f)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ScaffoldPullbackNativeLift.cocartesianScaffoldPullbackNativeLiftPre p q b)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ScaffoldPullbackNativeLift.cocartesianScaffoldPullbackNativeLiftPre p q a)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ScaffoldPullbackNativeLift.cocartesianScaffoldPullbackNativeLiftPre_naturality p q f) r

/-- 同じ相対比較は、既存の元の native core 比較を厳密に保持する。 -/
lemma cocartesianScaffoldNativeLiftBoundaryPre_ι :
    cocartesianScaffoldNativeLiftBoundaryPre p q f r ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ScaffoldPullbackNativeLift.cocartesianScaffoldPullbackMarkedLiftRestriction p q f)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ScaffoldPullbackNativeLift.cocartesianScaffoldPullbackNativeLiftPre p q a).app (Opposite.op ⦋0⦌) r) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeLiftPre p q f) r ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ScaffoldPullbackNativeLift.cocartesianScaffoldPullbackNativeLiftPre p q b :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.kanSquareFiberMap_ι _ _ _ _ _ _

/-- 任意の単射な境界で、この同じ元の native 境界固定比較は同値。 -/
lemma cocartesianScaffoldNativeLiftBoundaryPre_isQCatEquivalence [Mono f.left] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (cocartesianScaffoldNativeLiftBoundaryPre p q f r) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.kanSquareFiberMap_isQCatEquivalence _ _ _ _ _ r
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ScaffoldPullbackNativeLift.cocartesianScaffoldPullbackNativeLiftPre_isQCatEquivalence p q b)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ScaffoldPullbackNativeLift.cocartesianScaffoldPullbackNativeLiftPre_isQCatEquivalence p q a)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
