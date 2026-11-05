module
public import SerrePositivity.KST.Fibration.IdentityFractionTriangle

/-! # 元の分数評価の恒等点を、実写像空間内で正規化する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {X Q : SSet.{u}} [Quasicategory Q] (F : X ⟶ Q) (W : Set (X _⦋1⦌))
  (hF : InvertsEdges F W) (x : X _⦋0⦌) (hx : PinchedHom.constant x 1 ∈ W)

/-- 元の評価が選んだ三角形を、同じ恒等 span の fiber の点として保持する。 -/
def chosenIdentityFractionTriangle :
    (vertexFiber (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangleProjection F W hF x x)
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.identityFixedMarkedSpan W x hx)) _⦋0⦌ :=
  ⟨(_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangleSection F W hF x x).app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.identityFixedMarkedSpan W x hx), by
    rw [pinchedConstant_zero]
    exact congrArg (fun m => m.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.identityFixedMarkedSpan W x hx))
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangleSection_projection F W hF x x)⟩

/-- 定値三角形も、同じ恒等 span の同じ実 fiber の点。 -/
def constantIdentityFractionTriangle :
    (vertexFiber (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangleProjection F W hF x x)
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.identityFixedMarkedSpan W x hx)) _⦋0⦌ :=
  ⟨SSet.yonedaEquiv (identityFractionTriangle F W hF x hx), by
    rw [pinchedConstant_zero, ← SSet.yonedaEquiv_comp,
      identityFractionTriangle_projection, SSet.yonedaEquiv_const]⟩

/-- 選択済み三角形と定値三角形は、恒等 span を固定した可縮な空間内で同値。 -/
def identityFractionTriangleIso : VertexIso
    (chosenIdentityFractionTriangle F W hF x hx)
    (constantIdentityFractionTriangle F W hF x hx) :=
  (vertexFiber_isContractibleKan (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangleProjection F W hF x x)
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.identityFixedMarkedSpan W x hx)).vertexIso _ _

/-- 分数評価の恒等点は、元の区間写像空間内で実際の恒等辺の点と同値。 -/
def identityFixedFractionEvaluationIso : VertexIso
    ((fixedFractionEvaluation F W hF x x).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.identityFixedMarkedSpan W x hx))
    (intervalMappingVertexOfEdge (SSet.Edge.id (F.app (Opposite.op ⦋0⦌) x))) := by
  have e := (identityFractionTriangleIso F W hF x hx).map
    (vertexFiberι (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangleProjection F W hF x x)
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.identityFixedMarkedSpan W x hx) ≫ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangleEvaluation F W hF x x)
  have hchosen : (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangleEvaluation F W hF x x).app (Opposite.op ⦋0⦌)
      (chosenIdentityFractionTriangle F W hF x hx).val =
      (fixedFractionEvaluation F W hF x x).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.identityFixedMarkedSpan W x hx) :=
    congrArg (fun m => m.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.identityFixedMarkedSpan W x hx))
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangleSection_evaluation F W hF x x)
  have hconstant : (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangleEvaluation F W hF x x).app (Opposite.op ⦋0⦌)
      (constantIdentityFractionTriangle F W hF x hx).val =
      intervalMappingVertexOfEdge (SSet.Edge.id (F.app (Opposite.op ⦋0⦌) x)) := by
    change (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangleEvaluation F W hF x x).app (Opposite.op ⦋0⦌)
      (SSet.yonedaEquiv (identityFractionTriangle F W hF x hx)) = _
    rw [← SSet.yonedaEquiv_comp, identityFractionTriangle_evaluation,
      SSet.yonedaEquiv_const]
  change VertexIso
    ((_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangleEvaluation F W hF x x).app (Opposite.op ⦋0⦌)
      (chosenIdentityFractionTriangle F W hF x hx).val)
    ((_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangleEvaluation F W hF x x).app (Opposite.op ⦋0⦌)
      (constantIdentityFractionTriangle F W hF x hx).val) at e
  rw [hchosen, hconstant] at e
  exact e

/-- 同じ比較を、元の写像空間内の一本の実際の辺としても取り出す。 -/
def identityFixedFractionEvaluationEdge :
    SSet.Edge ((fixedFractionEvaluation F W hF x x).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.identityFixedMarkedSpan W x hx))
      (intervalMappingVertexOfEdge (SSet.Edge.id (F.app (Opposite.op ⦋0⦌) x))) :=
  SSet.Edge.ofTruncated (Classical.choose (homotopyCategory_homMk_surjective _ _
    (identityFixedFractionEvaluationIso F W hF x hx).hom))

/-- 亜群化後の元の比較も、元の恒等 span の像を同じ恒等点へ送る。 -/
def identityFractionMappingComparisonIso : VertexIso
    ((_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionMappingComparison F W hF x x).app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionMap (fixedMarkedSpans X W x x)).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.identityFixedMarkedSpan W x hx)))
    (intervalMappingVertexOfEdge (SSet.Edge.id (F.app (Opposite.op ⦋0⦌) x))) := by
  have e := VertexIso.map (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionMappingComparisonIso F W hF x x)
    (evaluateFunctorAt (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.identityFixedMarkedSpan W x hx))
  simp only [evaluateFunctorAt_functorVertex] at e
  exact e ≪≫ identityFixedFractionEvaluationIso F W hF x hx

end SerrePositivity.KST.Fibration
