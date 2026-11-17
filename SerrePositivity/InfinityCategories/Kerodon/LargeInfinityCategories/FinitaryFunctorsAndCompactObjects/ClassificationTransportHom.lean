module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningDiagramFiberNaturality
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ClassificationTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningDiagramHomArrow

/-!
概要：既存の全分類同型の順射を、同じ元の底上の射と実fiberの像へ合わせる。
方針：元のasIsoの順射と同じ端点の係数移送を外して、全straighteningの評価則へ接続する。
規約：既存の分類同型と同じ射・底の等式・前合成同値の証拠を保持する。
使われ方：元のraw側の全分類同型の指定単位の照合。
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

noncomputable section

namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects

private lemma classificationTransportEqMp_heq_iff {α β : Sort u} (h : α = β) (a : α)
    {γ : Sort _} (b : γ) : HEq (Eq.mp h a) b ↔ HEq a b := by cases h; rfl

/-- 元の分類同型は、元の同じ底上の可逆な辺の分類像を端点の等式で移したもの。 -/
lemma leftClassification_of_precompositionEquivalence_value {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) (ef : IsPrecompositionEquivalence f) :
    HEq (leftClassification_of_precompositionEquivalence p q f hf ef)
      (VertexIso.map (leftFibrationInfinityVertexIsoOfPrecompositionEquivalence p q f hf ef)
        (leftStraighteningInfinityMap B)) := by
  unfold leftClassification_of_precompositionEquivalence
  simp only [classificationTransportEqMp_heq_iff]
  rfl

private lemma classificationTransportIsoHom_heq {D : Type u} [Category.{v} D]
    {a b a' b' : D} (ha : a = a') (hb : b = b')
    (e : a ≅ b) (e' : a' ≅ b') (h : HEq e e') : HEq e.hom e'.hom := by
  subst a' b'
  cases h
  rfl

/-- 元の分類同型の順射は、同じ元の底上の射の全straighteningの像そのもの。 -/
lemma leftClassification_of_precompositionEquivalence_hom {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) (ef : IsPrecompositionEquivalence f) :
    (leftClassification_of_precompositionEquivalence p q f hf ef).hom =
      leftStraighteningInfinityDiagramHom p q f hf := by
  have h := classificationTransportIsoHom_heq
    (congrArg HomotopyCategory.mk (leftStraighteningInfinityDiagram_vertex p))
    (congrArg HomotopyCategory.mk (leftStraighteningInfinityDiagram_vertex q))
    _ _ (leftClassification_of_precompositionEquivalence_value p q f hf ef)
  change HEq (leftClassification_of_precompositionEquivalence p q f hf ef).hom
    ((hoFunctor.map (leftStraighteningInfinityMap B)).toFunctor.map
      (SSet.Truncated.HomotopyCategory.homMk (leftFibrationInfinityEdge p q f hf).toTruncated)) at h
  exact eq_of_heq (h.trans (leftStraighteningInfinityDiagramHom_heq p q f hf).symm)
/-- 元の分類同型の順射の同じ評価は、元の指定fiber同型で共役した同じ実fiber射の像。 -/
lemma leftClassification_of_precompositionEquivalence_fiber_value {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) (ef : IsPrecompositionEquivalence f)
    (b : B _⦋0⦌) :
    functorHomEvaluate (leftClassification_of_precompositionEquivalence p q f hf ef).hom (ULift.up b) =
      (leftStraighteningInfinityDiagram_fiberIso p b).hom ≫
        HomotopyCategory.homMk (coherentNerveEdge
          (show leftFibrationFiberObject b (leftFibrationObjectOf p) ⟶
            leftFibrationFiberObject b (leftFibrationObjectOf q) from vertexFiberMap p q f hf b)) ≫
        (leftStraighteningInfinityDiagram_fiberIso q b).inv := by
  rw [leftClassification_of_precompositionEquivalence_hom]
  exact leftStraighteningInfinityDiagramHom_actualFiber_value p q f hf b

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects

end
