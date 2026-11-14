module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StandardRowCochainNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictBarUnnormalizedFunctor
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarTotalValues

/-!
概要：元のcoherent barの比較に使う各列の、strict図式の自然変換への自然性。
方針：元の射列の余積包含の自然性と、同じ行のcochainの自然性を合成する。
規約：全単体のラベルと全内部次数を保つ。比較射は選び直さない。
使われ方：3b-3 R6、同じ全複体比較とnative余錐の高次成分の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

variable (A : Type u) [CommRing A] (J : Type) [SmallCategory J]

local instance : HasCoproducts.{0} (Complex A) := fun _ =>
  HomologicalComplex.instHasColimitsOfShape
local instance : HasCoproducts.{u} (Complex A) := fun _ =>
  HomologicalComplex.instHasColimitsOfShape

/-- 元の全射列のシフト前の列は、元の自然変換の同じ先頭成分に自然。 -/
lemma smallStrictBarUnshiftedColumn_naturality
    {F G : J ⥤ ModuleCategory A PUnit.{1}} (η : F ⟶ G)
    (s : dgCoherentBarIndex ((SSet.uliftFunctor.{u, 0}).obj (nerve J)))
    (p q : ℤ) (h : p + -(s.1 : ℤ) = q) :
    (smallStrictBarUnshiftedColumn A F s).v p q h ≫
        ((strictBarTotalComplexFunctor A J).map η).f q =
      ((moduleEvaluation A PUnit.{1} PUnit.unit).map (η.app (s.2.down.obj 0))).f p ≫
        (smallStrictBarUnshiftedColumn A G s).v p q h := by
  let t : smallStrictBarCoefficientDiagram A F ⟶ smallStrictBarCoefficientDiagram A G :=
    Functor.whiskerRight η (moduleEvaluation A PUnit.{1} PUnit.unit)
  rw [smallStrictBarUnshiftedColumn_v, smallStrictBarUnshiftedColumn_v, Category.assoc]
  change _ ≫ (standardRowCochain A
      (simplicialReplacement (smallStrictBarCoefficientDiagram A F)) s.1).v p q h ≫
      ((directSumTotalFunctor A).map (simplicialReplacementMap t)).f q = _
  rw [standardRowCochain_naturality]
  have hi := congrArg (fun f => f.f p) (ι_simplicialReplacementMap t (op ⦋s.1⦌) s.2.down)
  simpa only [t, Functor.whiskerRight_app, HomologicalComplex.comp_f, Category.assoc] using
    congrArg (fun f => f ≫ (standardRowCochain A
      (simplicialReplacement (smallStrictBarCoefficientDiagram A G)) s.1).v p q h) hi

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
