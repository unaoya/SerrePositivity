module
public import SerrePositivity.KST.Fibration.IdentityFractionEvaluation
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.FixedFractionCosliceGroupoid
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.MappingSpaceIntervalVertices

/-! # 元の coslice 評価の恒等点を、同じ coslice fiber 内で正規化する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
attribute [local instance] vertexFiber_kanComplex_of_leftFibration
variable {X Q : SSet.{u}} [Quasicategory Q] (F : X ⟶ Q) (W : Set (X _⦋1⦌))
  (hF : InvertsEdges F W) (x : X _⦋0⦌) (hx : PinchedHom.constant x 1 ∈ W)

/-- 恒等辺から作った coslice fiber の元の点は、区間模型でも恒等辺そのもの。 -/
theorem cosliceIdentityFiber_interval {Q : SSet.{u}} (y : Q _⦋0⦌) :
    (cosliceFiberToIntervalMappingSpace y y).app (Opposite.op ⦋0⦌)
      (edgeToCosliceFiberVertex (SSet.Edge.id y)) =
      intervalMappingVertexOfEdge (SSet.Edge.id y) := by
  rw [cosliceFiberToIntervalMappingSpace_vertex]
  exact congrArg intervalMappingVertexOfEdge ((cosliceFiberVertexEquiv y y).apply_symm_apply _)

/-- 元の全 span 族の恒等点の評価は、同じ実 coslice fiber 内で恒等点と同値。 -/
def identityFixedFractionCosliceEvaluationIso : VertexIso
    ((_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionCosliceEvaluation F W hF x x).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.identityFixedMarkedSpan W x hx))
    (edgeToCosliceFiberVertex (SSet.Edge.id (F.app (Opposite.op ⦋0⦌) x))) := by
  have e := VertexIso.map (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionCosliceComparisonIso F W hF x x)
    (evaluateFunctorAt (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.identityFixedMarkedSpan W x hx))
  simp only [evaluateFunctorAt_functorVertex] at e
  have he := e ≪≫ identityFixedFractionEvaluationIso F W hF x hx
  have hc := cosliceFiberToIntervalMappingSpace_isQCatEquivalence
    (F.app (Opposite.op ⦋0⦌) x) (F.app (Opposite.op ⦋0⦌) x)
  have hi : VertexIso
      ((cosliceFiberToIntervalMappingSpace (F.app (Opposite.op ⦋0⦌) x)
        (F.app (Opposite.op ⦋0⦌) x)).app (Opposite.op ⦋0⦌)
          (edgeToCosliceFiberVertex (SSet.Edge.id (F.app (Opposite.op ⦋0⦌) x))))
      (intervalMappingVertexOfEdge (SSet.Edge.id (F.app (Opposite.op ⦋0⦌) x))) :=
    eqToIso (congrArg SSet.HomotopyCategory.mk (cosliceIdentityFiber_interval _))
  exact hc.isFullyFaithful.toHoFullyFaithful.preimageIso (he ≪≫ hi.symm)

/-- 同じ亜群化後の coslice 比較でも、元の恒等 span の像を恒等点へ正規化できる。 -/
def identityFractionCosliceGroupoidComparisonIso : VertexIso
    ((_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionCosliceGroupoidComparison F W hF x x).app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionMap (fixedMarkedSpans X W x x)).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.identityFixedMarkedSpan W x hx)))
    (edgeToCosliceFiberVertex (SSet.Edge.id (F.app (Opposite.op ⦋0⦌) x))) := by
  have e := VertexIso.map (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionCosliceGroupoidComparisonIso F W hF x x)
    (evaluateFunctorAt ((_root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionMap (fixedMarkedSpans X W x x)).app
      (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.identityFixedMarkedSpan W x hx)))
  simp only [evaluateFunctorAt_functorVertex] at e
  have he := e ≪≫ identityFractionMappingComparisonIso F W hF x hx
  have hc := cosliceFiberToIntervalMappingSpace_isQCatEquivalence
    (F.app (Opposite.op ⦋0⦌) x) (F.app (Opposite.op ⦋0⦌) x)
  have hi : VertexIso
      ((cosliceFiberToIntervalMappingSpace (F.app (Opposite.op ⦋0⦌) x)
        (F.app (Opposite.op ⦋0⦌) x)).app (Opposite.op ⦋0⦌)
          (edgeToCosliceFiberVertex (SSet.Edge.id (F.app (Opposite.op ⦋0⦌) x))))
      (intervalMappingVertexOfEdge (SSet.Edge.id (F.app (Opposite.op ⦋0⦌) x))) :=
    eqToIso (congrArg SSet.HomotopyCategory.mk (cosliceIdentityFiber_interval _))
  exact hc.isFullyFaithful.toHoFullyFaithful.preimageIso (he ≪≫ hi.symm)

end SerrePositivity.KST.Fibration
