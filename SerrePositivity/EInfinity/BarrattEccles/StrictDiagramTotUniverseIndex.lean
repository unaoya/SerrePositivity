module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotBKNativeClassification
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotalizationInput
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FunctorComparison.LiftedShapeNerveIso

/-!
概要：大きい二重反対添字を、元のstrict BE図式の同じULift添字へ戻す。
方針：元のAsSmall nerve同型と二重反対圏の厳密な逆関手のnerve同型を合成する。
規約：IS-W2 R02〜R03の既存の添字移送則。元の全図式との射の等式を保つ。
使われ方：同じ指定BK点から得たjoin錐を元のΔ添字へ輸送する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped Simplicial

/-- 元の二重反対の二つの厳密な逆関手のnerve同型。 -/
def strictBETotOpOpNerveIso (K : Type u) [SmallCategory K] : nerve Kᵒᵖᵒᵖ ≅ nerve K :=
  nerveIsoOfStrictInverse (opOpEquivalence K).functor (opOpEquivalence K).inverse rfl rfl

/-- 同じ大きい添字を、元の同じULift添字へ戻す指定同型。 -/
def strictBETotUniverseIndexIso (K : Type u) [SmallCategory K] :
    nerve (AsSmall.{u+1} Kᵒᵖᵒᵖ) ≅ (SSet.uliftFunctor.{u+1,u}).obj (nerve K) :=
  (nerveAsSmallIso.{u,u+1} Kᵒᵖᵒᵖ).symm ≪≫
    (SSet.uliftFunctor.{u+1,u}).mapIso (strictBETotOpOpNerveIso K)

/-- 同じ添字同型で戻すと、元の全strict BE図式そのものになる。 -/
theorem strictBETotUniverseSourceDiagram_index (A : Type u) [CommRing A]
    (F : AsSmall.{u} SimplexCategory ⥤ (operad A).Algebra) :
    strictBETotUniverseSourceDiagram A (AsSmall.{u} SimplexCategory) F =
      (strictBETotUniverseIndexIso (AsSmall.{u} SimplexCategory)).hom ≫
        strictBECosimplicialDiagram A F := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro σ
  rfl

end SerrePositivity.EInfinity.BarrattEccles
