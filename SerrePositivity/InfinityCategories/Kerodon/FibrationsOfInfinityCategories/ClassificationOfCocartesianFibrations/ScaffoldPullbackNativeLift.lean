module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ScaffoldPullbackNativeCore
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PullbackNativeLiftRestriction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.Reflection
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanFibrationEquivalenceLifting

/-!
概要：元の native core と同じ scaffold 比較の宇宙を、セル貼合せの宇宙へ揃える。
方針：同じ比較と制限を ULift 関手で移し、同値性・自然性・Kan 性を保つ。
規約：元の全相対 Hom と同じ底上の制限を使う。
使われ方：既存のセル付加の native 延長空間からの比較。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ScaffoldPullbackNativeLift
variable {C : Type u} [Category.{u} C] {E F : SSet.{u}}
  (p : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] (q : F ⟶ nerve C)
  [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration q]

local instance (z : Over (nerve C)) : InnerFibration (pullback.fst z.hom q) :=
  ⟨innerFibrations.pullback_fst z.hom q (InnerFibration.mem (q := q))⟩

local instance (z : Over (nerve C)) :
    Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldPullbackMarkedHom p q z) :=
  inferInstanceAs (Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorSpace q _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldPullbackMark p z)))

local instance (z : Over (nerve C)) : KanComplex
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.cocartesianRelativeFunctorSpace (pullback.fst z.hom p) (pullback.fst z.hom q))) :=
  inferInstanceAs (KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.cocartesianRelativeFunctorSpace (pullback.fst z.hom p) (pullback.fst z.hom q)) : SSet.{u}))

/-- 同じ元の native core 比較を、分類先と同じ宇宙へ移す。 -/
def cocartesianScaffoldPullbackNativeLiftPre (a : Over (nerve C)) :=
  (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ScaffoldPullbackNativeCore.cocartesianScaffoldPullbackNativeCorePre p q a)

/-- 同じ scaffold core の制限を、分類先と同じ宇宙へ移す。 -/
def cocartesianScaffoldPullbackMarkedLiftRestriction {a b : Over (nerve C)} (f : a ⟶ b) :=
  (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldPullbackMarkedCoreRestriction p q f)

/-- 宇宙を揃えた同じ native core 比較も同値。 -/
lemma cocartesianScaffoldPullbackNativeLiftPre_isQCatEquivalence (a : Over (nerve C)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (cocartesianScaffoldPullbackNativeLiftPre p q a) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.isQCatEquivalence_ulift_iff_of_kan _).mpr
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ScaffoldPullbackNativeCore.cocartesianScaffoldPullbackNativeCorePre_isQCatEquivalence p q a)

/-- 同じ大きい宇宙の native core 比較は、既存の native 制限と厳密に可換。 -/
lemma cocartesianScaffoldPullbackNativeLiftPre_naturality
    {a b : Over (nerve C)} (f : a ⟶ b) :
    cocartesianScaffoldPullbackNativeLiftPre p q b ≫
      cocartesianScaffoldPullbackMarkedLiftRestriction p q f =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeLiftPre p q f ≫ cocartesianScaffoldPullbackNativeLiftPre p q a := by
  change (SSet.uliftFunctor.{u + 1, u}).map _ ≫ (SSet.uliftFunctor.{u + 1, u}).map _ =
    (SSet.uliftFunctor.{u + 1, u}).map _ ≫ (SSet.uliftFunctor.{u + 1, u}).map _
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ScaffoldPullbackNativeCore.cocartesianScaffoldPullbackNativeCorePre_naturality]

/-- 大きい宇宙の同じ scaffold core の単射制限は Kan fibration。 -/
lemma cocartesianScaffoldPullbackMarkedLiftRestriction_fibration
    {a b : Over (nerve C)} (f : a ⟶ b) [Mono f.left] :
    Fibration (cocartesianScaffoldPullbackMarkedLiftRestriction p q f) := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldPullbackMarkedCoreRestriction_fibration p q f
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.fibration_uliftFunctor_map _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ScaffoldPullbackNativeLift
