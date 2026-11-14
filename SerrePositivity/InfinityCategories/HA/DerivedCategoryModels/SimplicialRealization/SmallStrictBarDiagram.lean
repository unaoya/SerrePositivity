module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.SmallDiagramShape
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictDiagramEvaluation
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.Diagram
import all SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.SmallDiagramShape
import all SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictDiagramEvaluation
import all SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.NerveInclusion

/-!
# 小さい strict 図式を既存 coherent bar の同じ入力へ渡す

## 概要
宇宙0の射列を係数環の宇宙経由で持ち上げ、既存の右 dg 加群の bar の入力を作る。

## 方針
既存の二段 ULift の同型と strict nerve を合成し、元の閉零射の列を照合する。

## 規約
元の射列・係数・高次零成分を保持し、係数環の宇宙を制限しない。

## 使われ方
HA 1.2.4。単体的置換と native coherent bar の具体的比較の入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits SerrePositivity.DifferentialGraded SSet
open scoped _root_.Simplicial
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Project.DerivedCategories
variable (A : Type u) [CommRing A] {J : Type} [SmallCategory J]

/-- 同じ小さい strict 図式を、係数環の宇宙での既存 coherent bar へ渡す。 -/
def smallStrictBarDiagram (F : J ⥤ ModuleCategory A PUnit.{1}) :
    (SSet.uliftFunctor.{u + 1, u}).obj ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) ⟶
      dgNerve A (RightModule A PUnit.{1}) :=
  (smallDiagramShapeIso.{u} (nerve J)).hom ≫
    strictDiagramNerve J (ModuleCategory A PUnit.{1}) F ≫
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A (RightModule A PUnit.{1})

/-- 全単体は、元の同じ射列から作る閉零射の列。 -/
theorem smallStrictBarDiagram_simplex (F : J ⥤ ModuleCategory A PUnit.{1}) {n : ℕ}
    (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n⦌) :
    coherentDiagramSimplex (smallStrictBarDiagram A F) s = closedNerveSimplex (s.down ⋙ F) := rfl

/-- 小さい射列の先頭の加群は、既存 bar の元の係数加群と厳密に一致する。 -/
theorem smallStrictBarDiagram_source (F : J ⥤ ModuleCategory A PUnit.{1})
    (s : dgCoherentBarIndex ((SSet.uliftFunctor.{u, 0}).obj (nerve J))) :
    dgCoherentBarSource A PUnit.{1} (smallStrictBarDiagram A F) s =
      ForgetEnrichment.to (Complex A) (F.obj (s.2.down.obj 0)) := rfl

/-- 同じ strict 図式の高次 prefix の係数は零。 -/
theorem smallStrictBarDiagram_higher (F : J ⥤ ModuleCategory A PUnit.{1})
    {n : ℕ} (hn : 0 < n)
    (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n + 1⦌) :
    coherentDiagramTopRaw (smallStrictBarDiagram A F) s = 0 := by
  exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion_higher A (RightModule A PUnit.{1}) (s.down ⋙ F)
    Finset.univ 0 (Fin.last (n + 1)) (-(n : ℤ))
    (coherentDiagramTop_card n) (coherentDiagramTop_min n) (coherentDiagramTop_max n)
    (by simp; omega) (by simp; omega)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
