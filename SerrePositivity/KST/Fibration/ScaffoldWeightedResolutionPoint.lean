module
public import SerrePositivity.KST.Fibration.ScaffoldTransportPointedCoefficient
public import SerrePositivity.KST.Fibration.OppositeKanResolutionEvaluation

/-! # 元の scaffold の同じ weighted 点を既存の左解像比較へ厳密に戻す -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
/-- fiber 点の値を変えず、底の頂点の表示だけを等号で変える。 -/
def vertexFiberPointReindex {E B : SSet.{u}} (q : E ⟶ B)
    {b b' : B _⦋0⦌} (h : b = b') (v : (vertexFiber q b) _⦋0⦌) :
    (vertexFiber q b') _⦋0⦌ :=
  ⟨v.val, v.property.trans (congrArg (fun z => PinchedHom.constant z 0) h)⟩

/-- 値を保つ表示は、同じ等号による標準の fiber 移送と一致する。 -/
theorem vertexFiberPointReindex_eq_transport {E B : SSet.{u}} (q : E ⟶ B)
    {b b' : B _⦋0⦌} (h : b = b') (v : (vertexFiber q b) _⦋0⦌) :
    vertexFiberPointReindex q h v =
      (eqToHom (congrArg (vertexFiber q) h)).app (Opposite.op ⦋0⦌) v := by
  subst b'
  rfl

namespace ScaffoldTransportComparisonSpan
variable {I : Type u} [Category.{u} I] {E : SSet.{u}}
  {p : E ⟶ nerve I} [LeftFibration p] (s : ScaffoldTransportComparisonSpan p)

/-- 分類値の表示変更を、元の表現と元の Kan 値を明記して固定する。 -/
theorem coefficientResolutionVertexEq (c : I) :
    (leftCoherentTransport p).app (Opposite.op ⦋0⦌) (ULift.up (nerveVertex c)) =
      spaceInfinityVertex (kanObjectOpFunctor.obj ((leftStrictTransportFunctor p).obj c)) := by
  simpa only [leftCoherentTransport, Functor.comp_obj] using
    kanDiagramCoherentNerve_vertex (leftStrictTransportFunctor p ⋙ kanObjectOpFunctor) c

private theorem fiberPoint_ext {E B : SSet.{u}} (q : E ⟶ B) (b : B _⦋0⦌)
    (v w : (vertexFiber q b) _⦋0⦌)
    (h : (vertexFiberι q b).app (Opposite.op ⦋0⦌) v =
      (vertexFiberι q b).app (Opposite.op ⦋0⦌) w) : v = w :=
  Subtype.ext h

/-- strict transport の忘却図式は元の単体集合値図式と厳密に一致。 -/
theorem strictTransportForget_eq :
    leftStrictTransportFunctor p ⋙ kanObjectForget = leftStrictTransportDiagram p := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro a b f
  rfl

/-- 元の weighted 射の係数作用を、元の図式を明記して左解像比較へ戻す。 -/
theorem coherentComparison_constant_resolution (c : I) :
    (SSet.uliftFunctor.{u + 1, u}).map
      (weightedNerveConstantLift (leftStrictTransportDiagram p) c) ≫
        leftCoherentTransportComparison p ≫
          CategoryTheory.Limits.pullback.fst pointedSpaceProjection (leftCoherentTransport p) =
    pointedSpaceLeftResolutionComparison ((leftStrictTransportFunctor p).obj c) ≫
      vertexFiberι pointedSpaceProjection
        (spaceInfinityVertex (kanObjectOpFunctor.obj ((leftStrictTransportFunctor p).obj c))) := by
  have h := oppositeKanUnstraighteningComparison_constant_resolution
    (leftStrictTransportFunctor p) c
  simpa only [leftCoherentTransportComparison, leftCoherentTransport,
    leftStrictTransportFunctor, kanObjectForget, leftStrictTransportDiagram, Functor.comp] using h

/-- 分類値を元の反転 Kan 空間の標準頂点へ同じ等号で移した weighted 点。 -/
def coefficientWeightedResolutionPoint (c : I) (v : (leftStrictTransport p c) _⦋0⦌) :
    (vertexFiber pointedSpaceProjection
      (spaceInfinityVertex (kanObjectOpFunctor.obj ((leftStrictTransportFunctor p).obj c))))
        _⦋0⦌ :=
  vertexFiberPointReindex pointedSpaceProjection
    (coefficientResolutionVertexEq (p := p) c) (s.coefficientWeightedPointedFiberPoint c v)

/-- 同じ weighted 点は、頂点の表示を揃えると左解像比較の元の係数点の実像と一致。 -/
theorem coefficientWeightedResolutionPoint_eq (c : I) (v : (leftStrictTransport p c) _⦋0⦌) :
    s.coefficientWeightedResolutionPoint c v =
      (pointedSpaceLeftResolutionComparison ((leftStrictTransportFunctor p).obj c)).app
        (Opposite.op ⦋0⦌) (ULift.up v) := by
  apply fiberPoint_ext pointedSpaceProjection
    (spaceInfinityVertex (kanObjectOpFunctor.obj ((leftStrictTransportFunctor p).obj c)))
  have h := congrArg (fun m => m.app (Opposite.op ⦋0⦌) (ULift.up v))
    (coherentComparison_constant_resolution (p := p) c)
  exact (s.coefficientWeightedPointedFiberPoint_val c v).trans h

end ScaffoldTransportComparisonSpan
end SerrePositivity.KST.Fibration
