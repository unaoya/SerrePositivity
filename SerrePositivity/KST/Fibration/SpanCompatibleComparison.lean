module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationSpanStrictification
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.RelativeFunctorEssentialExtension
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.RelativeFunctorEvaluation

/-! # 元の指定 span との相対三角比較をデータとして保持する、底上の実比較 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- 指定した元の span の二脚と、その同じ span 上の相対三角比較を保持する。 -/
structure SpanCompatibleComparison {E F Z B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) (r : Z ⟶ B)
    (a : Z ⟶ E) (b : Z ⟶ F) (ha : a ≫ p = r) (hb : b ≫ q = r) where
  hom : E ⟶ F
  over : hom ≫ q = p
  triangle : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex q r (a ≫ hom) (by rw [Category.assoc, over, ha]))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex q r b hb)
  equivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence hom

/-- 元の指定 span を保つ比較は、同じ相対前合成の本質的全射性から構成できる。 -/
theorem nonempty_spanCompatibleComparison {E F Z B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q] (r : Z ⟶ B)
    (a : Z ⟶ E) (b : Z ⟶ F) (ha : a ≫ p = r) (hb : b ≫ q = r)
    (ea : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence a) (eb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence b) :
    Nonempty (SpanCompatibleComparison p q r a b ha hb) := by
  have : Quasicategory F := quasicategory_of_innerFibration q
  let a' : Over.mk r ⟶ Over.mk p := Over.homMk a ha
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeFunctorOverPre_isQCatEquivalence q a' ea
  obtain ⟨v, ⟨h⟩⟩ := he.choose.isEssentiallySurjective (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex q r b hb)
  obtain ⟨f, hf, hv⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.exists_relativeFunctorVertex q p v
  rw [← hv] at h
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre q a').app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex q p f hf))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex q r b hb) at h
  have ht := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre_vertex q a' f hf
  have hn : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex q r (a ≫ f) (by rw [Category.assoc, hf, ha]))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex q r b hb) :=
    (eqToIso (congrArg HomotopyCategory.mk ht)).symm ≪≫ h
  have h' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (a ≫ f) b := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map hn
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom Z).map q) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex r))
  have hcomp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (a ≫ f) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_iff_of_homotopy h'.simplicialHomotopy
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.simplicialHomotopyOfFunctorEdge_vertex_isInvertible
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.edge h') (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.edge_isInvertible h'))).mpr eb
  exact ⟨⟨f, hf, hn, ea.cancel_left hcomp⟩⟩

/-- 選ぶ対象には相対三角比較も含め、元の span との対応を保持する。 -/
def spanCompatibleComparison {E F Z B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q] (r : Z ⟶ B)
    (a : Z ⟶ E) (b : Z ⟶ F) (ha : a ≫ p = r) (hb : b ≫ q = r)
    (ea : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence a) (eb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence b) :
    SpanCompatibleComparison p q r a b ha hb :=
  Classical.choice (nonempty_spanCompatibleComparison p q r a b ha hb ea eb)

/-- 保持した同じ相対三角比較を、元の共通全空間の指定点で評価する。 -/
def SpanCompatibleComparison.pointIso {E F Z B : SSet.{u}}
    {p : E ⟶ B} {q : F ⟶ B} {r : Z ⟶ B}
    {a : Z ⟶ E} {b : Z ⟶ F} {ha : a ≫ p = r} {hb : b ≫ q = r}
    (c : SpanCompatibleComparison p q r a b ha hb) (z : Z _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorEvaluate q r z).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex q r (a ≫ c.hom) (by rw [Category.assoc, c.over, ha])))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorEvaluate q r z).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex q r b hb)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map c.triangle (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorEvaluate q r z)

end SerrePositivity.KST.Fibration
