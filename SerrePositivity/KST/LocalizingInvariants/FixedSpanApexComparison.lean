module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.FixedMarkedSpanQuasicategory
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePathIso

/-!
概要：両端固定の分母付き span の頂点は、反転後には固定した第一終点と自然同型。
方針：分母の全族を点ごとに可逆なホモトピーに展開し、厳密な終点条件を使う。
規約：頂点ごとの同型の選択ではなく、全 span の実関手同型を与える。
使われ方：分母付き span の射を反転する評価と局所的な span 族の解析。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

def markedSpanApex (X : SSet.{u}) (W : Set (X _⦋1⦌)) : markedSpans X W ⟶ X :=
  markedSpanInclusion X W ≫ (pre horn₂₀.ι₀₁).app X ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))

def fixedMarkedSpanApex (X : SSet.{u}) (W : Set (X _⦋1⦌)) (x y : X _⦋0⦌) :
    fixedMarkedSpans X W x y ⟶ X := fixedMarkedSpanInclusion X W x y ≫ markedSpanApex X W

lemma markedSpanBoundary_source (X : SSet.{u}) (W : Set (X _⦋1⦌)) :
    markedSpanBoundary X W ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
      (⟨stdSimplex.obj₀Equiv.symm (0 : Fin 2), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary 0 0⟩ :
        (boundary 1 : SSet.{u}) _⦋0⦌) = markedSpanSource X W := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro v
  change (markedSpanSource X W).app (Opposite.op ⦋n⦌)
    ((markedSpans X W).map (𝟙 _) v) = _
  rw [CategoryTheory.Functor.map_id_apply]

lemma fixedMarkedSpan_source (X : SSet.{u}) (W : Set (X _⦋1⦌)) (x y : X _⦋0⦌) :
    fixedMarkedSpanInclusion X W x y ≫ markedSpanSource X W = SSet.const x := by
  rw [← markedSpanBoundary_source, ← Category.assoc, fixedMarkedSpanInclusion,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.const_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex]
  change SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 0) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]

lemma evaluateFunctorAt_postcomp {A X Q : SSet.{u}} (F : X ⟶ Q) (a : A _⦋0⦌) :
    (ihom A).map F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a ≫ F := rfl

def equivalenceSpanFirstEdgeIso {A Q : SSet.{u}} [Quasicategory Q]
    (f : A ⟶ equivalenceSpans Q) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      ((f ≫ equivalenceSpanInclusion Q ≫ (pre horn₂₀.ι₀₁).app Q) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
      ((f ≫ equivalenceSpanInclusion Q ≫ (pre horn₂₀.ι₀₁).app Q) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) := by
  let L := f ≫ equivalenceSpanInclusion Q ≫ (pre horn₂₀.ι₀₁).app Q
  have hv : ∀ v : A _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex (L.app (Opposite.op ⦋0⦌) v) := by
    intro v
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (f.app (Opposite.op ⦋0⦌) v)
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorIsoOfEquivalenceHomotopy (uncurry L) (by
    intro v
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge_curry, curry_uncurry]
    exact hv v)
  simpa only [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, curry_uncurry] using h

def fixedMarkedSpanApexImageIso {X Q : SSet.{u}} [Quasicategory Q] (F : X ⟶ Q)
    (W : Set (X _⦋1⦌)) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F W) (x y : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (fixedMarkedSpanApex X W x y ≫ F)
      (SSet.const (F.app (Opposite.op ⦋0⦌) x)) := by
  have h := equivalenceSpanFirstEdgeIso
    (fixedMarkedSpanInclusion X W x y ≫ invertedSpanMap F W hF)
  simp only [Category.assoc, ← Category.assoc (invertedSpanMap F W hF),
    invertedSpanMap_inclusion] at h
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (fixedMarkedSpanApex X W x y ≫ F)
    ((fixedMarkedSpanInclusion X W x y ≫ markedSpanSource X W) ≫ F) at h
  rw [fixedMarkedSpan_source, SSet.const_comp] at h
  exact h

end SerrePositivity.KST.LocalizingInvariants
