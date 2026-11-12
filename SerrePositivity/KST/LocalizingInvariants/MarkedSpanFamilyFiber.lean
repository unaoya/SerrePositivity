module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.MarkedSpanFamilies

/-!
概要：第一終点固定の span 族の第二終点 fiber は、元の両端固定 span と実同型。
方針：境界図式の二つの端点条件と、二重の頂点 fiber の条件を往復する。
規約：射と全単体上の厳密な往復。使われ方：族の fiber ごとの亜群化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma markedSpanBoundary_target (X : SSet.{u}) (W : Set (X _⦋1⦌)) :
    markedSpanBoundary X W ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
      (⟨stdSimplex.obj₀Equiv.symm (1 : Fin 2), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary 0 1⟩ :
        (boundary 1 : SSet.{u}) _⦋0⦌) = markedSpanTarget X W := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro v
  change (markedSpanTarget X W).app (Opposite.op ⦋n⦌)
    ((markedSpans X W).map (𝟙 _) v) = _
  rw [CategoryTheory.Functor.map_id_apply]

lemma fixedMarkedSpan_target (X : SSet.{u}) (W : Set (X _⦋1⦌)) (x y : X _⦋0⦌) :
    fixedMarkedSpanInclusion X W x y ≫ markedSpanTarget X W = SSet.const y := by
  rw [← markedSpanBoundary_target, ← Category.assoc, fixedMarkedSpanInclusion,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.const_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex]
  change SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant y 0) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]

lemma markedSpanBoundary_of_endpoints {A X : SSet.{u}} (W : Set (X _⦋1⦌))
    (f : A ⟶ markedSpans X W) (x y : X _⦋0⦌)
    (hx : f ≫ markedSpanSource X W = SSet.const x)
    (hy : f ≫ markedSpanTarget X W = SSet.const y) :
    f ≫ markedSpanBoundary X W = SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingBoundary x y)) := by
  rw [markedSpanBoundary, ← curry_natural_left, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_naturality, hx, hy]
  apply uncurry_injective
  rw [uncurry_curry, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]
  rfl

variable (X : SSet.{u}) (W : Set (X _⦋1⦌)) (x y : X _⦋0⦌)

def fixedMarkedSpanToFamily : fixedMarkedSpans X W x y ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamily X W x :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift _ _ (fixedMarkedSpanInclusion X W x y) (fixedMarkedSpan_source X W x y)

lemma fixedMarkedSpanToFamily_inclusion : fixedMarkedSpanToFamily X W x y ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (markedSpanSource X W) x = fixedMarkedSpanInclusion X W x y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι _ _ _ _

def fixedMarkedSpanToFamilyFiber : fixedMarkedSpans X W x y ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection X W x) y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift _ _ (fixedMarkedSpanToFamily X W x y) (by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection, ← Category.assoc, fixedMarkedSpanToFamily_inclusion,
      fixedMarkedSpan_target])

def markedSpanFamilyFiberToFixed : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection X W x) y ⟶
    fixedMarkedSpans X W x y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection X W x) y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (markedSpanSource X W) x)
    (markedSpanBoundary_of_endpoints W _ x y (by
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const]) (by
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection X W x) y ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection X W x = _
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp _ _))

lemma markedSpanFamilyFiberToFixed_inclusion : markedSpanFamilyFiberToFixed X W x y ≫
    fixedMarkedSpanInclusion X W x y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection X W x) y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (markedSpanSource X W) x :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι _ _ _ _

def markedSpanFamilyFiberIso : fixedMarkedSpans X W x y ≅
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection X W x) y where
  hom := fixedMarkedSpanToFamilyFiber X W x y
  inv := markedSpanFamilyFiberToFixed X W x y
  hom_inv_id := by
    have : Mono (fixedMarkedSpanInclusion X W x y) := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.vertexFiberι_mono _ _
    apply (cancel_mono (fixedMarkedSpanInclusion X W x y)).mp
    rw [Category.assoc, markedSpanFamilyFiberToFixed_inclusion,
      ← Category.assoc, fixedMarkedSpanToFamilyFiber, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι,
      fixedMarkedSpanToFamily_inclusion, Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection X W x) y)).mp
    rw [Category.assoc, fixedMarkedSpanToFamilyFiber, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι, Category.id_comp]
    apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (markedSpanSource X W) x)).mp
    rw [Category.assoc, fixedMarkedSpanToFamily_inclusion, markedSpanFamilyFiberToFixed_inclusion]

end SerrePositivity.KST.LocalizingInvariants
