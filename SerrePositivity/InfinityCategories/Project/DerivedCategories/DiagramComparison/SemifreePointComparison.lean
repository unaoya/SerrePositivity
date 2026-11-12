module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.InfinityCategory
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSemifreeModules
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGQuasiEquivalenceNerve
public import SerrePositivity.DifferentialGraded.Module.Left.CategoryComparison
import all SerrePositivity.InfinityCategories.Project.DerivedCategories.InfinityCategory
import all SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeSubcategory
import all SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSemifreeModules
import all SerrePositivity.DifferentialGraded.Module.Left.CategoryComparison

/-!
# 一点 dg 加群の半自由模型と D(A) の比較

## 概要
一点 dg 圏上の半自由加群を評価して、既存 D(A) との実際の準圏同値を得る。

## 方針
全 Hom の評価同型を半自由部分圏へ制限し、定数加群で本質的全射性を示す。

## 規約
bar の既存の余錐を同じ D(A) へ移すための比較。模型を新しく定義し直さない。

## 使われ方
HTT 4.2.4.1、HA 1.2.4。strict 図式の bar 実現の半自由複体への移送。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SerrePositivity.DifferentialGraded
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open SerrePositivity.InfinityCategories.Project.DerivedCategories

variable (A : Type u) [CommRing A]

/-- 一点 dg 圏上の半自由加群を、その唯一の値の半自由複体へ送る。 -/
def semifreePointEvaluation : DGFunctor A (SemifreeDGModules A PUnit.{1}) (Semifree A) where
  obj M := ⟨(moduleEvaluationDG A PUnit.{1} PUnit.unit).obj M.val,
    (Semifree.complexSemifree_evaluation A (ForgetEnrichment.of (Complex A) M.val)).mpr M.property⟩
  map M N := (moduleEvaluationDG A PUnit.{1} PUnit.unit).map M.val N.val
  map_id M := (moduleEvaluationDG A PUnit.{1} PUnit.unit).map_id M.val
  map_comp M N P := (moduleEvaluationDG A PUnit.{1} PUnit.unit).map_comp M.val N.val P.val

/-- 半自由複体を一点 dg 圏上の同じ半自由加群として読む。 -/
def semifreePointConstant : DGFunctor A (Semifree A) (SemifreeDGModules A PUnit.{1}) where
  obj X := ⟨(ringConstantDG A).obj X.val, X.property⟩
  map X Y := (ringConstantDG A).map X.val Y.val
  map_id X := (ringConstantDG A).map_id X.val
  map_comp X Y Z := (ringConstantDG A).map_comp X.val Y.val Z.val

/-- 一点評価は半自由模型上でも dg 準同値。 -/
theorem semifreePointEvaluation_quasiEquivalence : QuasiEquivalence (semifreePointEvaluation A) := by
  refine ⟨?_, ?_⟩
  · intro M N
    exact (ringEvaluationDG_quasiEquivalence A).1 M.val N.val
  · refine ⟨?_⟩
    intro X
    let x := ForgetEnrichment.to (Complex A) X.as
    let M := (semifreePointConstant A).obj x
    exact ⟨(toHomotopy A (SemifreeDGModules A PUnit.{1})).obj
      (ForgetEnrichment.of (Complex A) M), ⟨Iso.refl _⟩⟩

/-- 既存 D(A) を終域とする一点半自由模型の全準圏同値。 -/
def semifreePointEquivalence :
    SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
      (dgModuleDerivedInfinityCategory A PUnit.{1}) (derivedInfinityCategory A) :=
  dgQuasiEquivalenceNerveEquivalence (semifreePointEvaluation A)
    (semifreePointEvaluation_quasiEquivalence A)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
