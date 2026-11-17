module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningDiagramHomEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationFiberEvaluationEdge
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningDiagramFiberComparison

/-!
概要：元の全図式の射の評価は、元の指定評価同型で共役した実際のfiber射。
方針：元の全自然性に実際のfiber射の像を代入し、同じ両端の等式で正規化する。
規約：結論は同じホモトピー圏の射の厳密な等式であり、任意の底上の射を扱う。
使われ方：元の二変数native比較の同じ全射と指定単位の評価。
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
noncomputable section

namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

private lemma straighteningFiberArrow_conjugation {D : Type u} [Category.{v} D]
    {a b x y x' y' : D} (hx : x = x') (hy : y = y')
    (l : a ⟶ x) (r : y ⟶ b) (f : x ⟶ y) (g : x' ⟶ y')
    (h : Arrow.mk f = Arrow.mk g) :
    Arrow.mk (l ≫ f ≫ r) =
      Arrow.mk ((l ≫ eqToHom hx) ≫ g ≫ (eqToHom hy.symm ≫ r)) := by
  subst x' y'
  have hf : f = g := (Arrow.mk_inj _ _).mp h
  subst g
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]

/-- 元の全図式の射の同じ評価は、同じ指定評価同型と実際のfiber射の像の共役。 -/
lemma leftStraighteningInfinityDiagramHom_actualFiber_arrow {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) (b : B _⦋0⦌) :
    Arrow.mk (functorHomEvaluate (leftStraighteningInfinityDiagramHom p q f hf) (ULift.up b)) =
      Arrow.mk ((leftStraighteningInfinityDiagram_fiberIso p b).hom ≫
        HomotopyCategory.homMk (coherentNerveEdge
          (show leftFibrationFiberObject b (leftFibrationObjectOf p) ⟶
            leftFibrationFiberObject b (leftFibrationObjectOf q) from vertexFiberMap p q f hf b)) ≫
        (leftStraighteningInfinityDiagram_fiberIso q b).inv) := by
  have h₀ := straighteningFiberArrow_conjugation
    (congrArg HomotopyCategory.mk (leftFibrationInfinityFiberEvaluation_vertex b (leftFibrationObjectOf p)))
    (congrArg HomotopyCategory.mk (leftFibrationInfinityFiberEvaluation_vertex b (leftFibrationObjectOf q)))
    ((leftStraighteningInfinityMap_evaluateIso b).app (leftFibrationInfinityVertex p)).hom
    ((leftStraighteningInfinityMap_evaluateIso b).app (leftFibrationInfinityVertex q)).inv
    _ _ (leftFibrationInfinityFiberEvaluation_hom_arrow p q f hf b)
  refine (leftStraighteningInfinityDiagramHom_fiber_arrow p q f hf b).trans (h₀.trans ?_)
  symm
  dsimp only [leftStraighteningInfinityDiagram_fiberIso, Iso.trans_hom, Iso.trans_inv,
    eqToIso.hom, eqToIso.inv]
  simp only [Category.assoc, Arrow.arrow_mk_eqToHom_comp]
  simp only [← Category.assoc, Arrow.arrow_mk_comp_eqToHom]
/-- 元の全図式の射の同じ評価と、同じ実際のfiber射の像の共役は同じホモトピー圏の射として等しい。 -/
lemma leftStraighteningInfinityDiagramHom_actualFiber_value {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) (b : B _⦋0⦌) :
    functorHomEvaluate (leftStraighteningInfinityDiagramHom p q f hf) (ULift.up b) =
      (leftStraighteningInfinityDiagram_fiberIso p b).hom ≫
        HomotopyCategory.homMk (coherentNerveEdge
          (show leftFibrationFiberObject b (leftFibrationObjectOf p) ⟶
            leftFibrationFiberObject b (leftFibrationObjectOf q) from vertexFiberMap p q f hf b)) ≫
        (leftStraighteningInfinityDiagram_fiberIso q b).inv :=
  (Arrow.mk_inj _ _).mp (leftStraighteningInfinityDiagramHom_actualFiber_arrow p q f hf b)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

end
