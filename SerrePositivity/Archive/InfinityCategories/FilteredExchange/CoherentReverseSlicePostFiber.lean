module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentReverseSlicePost
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentHomSlicePost
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CompositionReverse
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberMap

/-!
概要：反対左 coslice の後合成を fiber に降ろし、元の反転 Hom 比較を保つ。
方針：包含後に元の正規化済み slice 反転と右 Hom 比較の自然性へ戻す。
規約：全反転 Hom を保持。使われ方：元の合成輸送比較の指定値への適用。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {C : Type v} [Category.{u} C] [SimplicialCategory C] (X : C) {Z W : C}
local notation "p(" A ")" => sliceUnderProjection
  (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm (coherentNerveVertex A)))
local notation "x" => SSet.opObjEquiv.symm (coherentNerveVertex X)

/-- 同じ反対左 coslice の後合成が誘導する、同じ始点の fiber の射。 -/
def coherentReverseSlicePostFiber (g : Z ⟶ W) : vertexFiber p(Z) x ⟶ vertexFiber p(W) x :=
  vertexFiberMap p(Z) p(W) (coherentReverseSlicePost g)
    (coherentReverseSlicePost_projection g) x

/-- 元の反転 Hom 比較は、同じ指定後合成と fiber 内で厳密に可換。 -/
lemma coherentReverseSliceFiberComparison_post (g : Z ⟶ W) :
    coherentReverseSliceFiberComparison X Z ≫ coherentReverseSlicePostFiber X g =
      SSet.opFunctor.map ((SSet.uliftFunctor.{v, u}).map (eHomWhiskerLeft SSet X g)) ≫
        coherentReverseSliceFiberComparison X W := by
  apply vertexFiber_hom_ext p(W) x
  change (coherentReverseSliceFiberComparison X Z ≫ vertexFiberι p(Z) x) ≫
      coherentReverseSlicePost g = _
  simp only [coherentReverseSliceFiberComparison, Category.assoc,
    pointSliceReverseFiberIso_ι]
  rw [coherentReverseSlicePost_from_over]
  have h := congrArg (fun k ↦ SSet.opFunctor.map k ≫
    (cofinalPointSliceOverOpIso (coherentNerveVertex W)).hom.left)
      (coherentHomSliceComparison_post (X := X) g)
  simpa only [SSet.opFunctor.map_comp, Category.assoc] using h

end SerrePositivity.InfinityCategories.F2
