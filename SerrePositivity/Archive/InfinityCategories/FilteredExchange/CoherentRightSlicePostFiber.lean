module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentHomSlicePost
public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentRightSlicePostComposition
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberMap

/-!
概要：元の右 slice 後合成を同じ始点の fiber へ降ろし、元の Hom 比較を保持する。
方針：底を固定する厳密等式から fiber 射を作り、包含後の全比較で照合する。
規約：元の射・比較を保持。使われ方：指定輸送比較の自然性への入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {C : Type v} [Category.{u} C] [SimplicialCategory C] (X : C) {Y Z W : C}
local notation "p(" A ")" =>
  sliceOverProjection (SSet.yonedaEquiv.symm (coherentNerveVertex A))
local notation "J(" A ")" => coherentHomComparison X A ≫
  pinchedHomToSliceFiber (coherentNerveVertex X) (coherentNerveVertex A)

/-- 元の終域射の右 slice 後合成が誘導する、同じ始点の fiber の射。 -/
def coherentRightSlicePostFiber (g : Y ⟶ Z) :
    vertexFiber p(Y) (coherentNerveVertex X) ⟶
      vertexFiber p(Z) (coherentNerveVertex X) :=
  vertexFiberMap p(Y) p(Z) (coherentRightSlicePost g)
    (coherentRightSlicePost_projection g) (coherentNerveVertex X)

/-- fiber の指定後合成は元の実右 slice への包含を厳密に保つ。 -/
lemma coherentRightSlicePostFiber_ι (g : Y ⟶ Z) :
    coherentRightSlicePostFiber X g ≫ vertexFiberι p(Z) (coherentNerveVertex X) =
      vertexFiberι p(Y) (coherentNerveVertex X) ≫ coherentRightSlicePost g := rfl

/-- 同じ元の二射の fiber 後合成も、元の合成を厳密に保持する。 -/
lemma coherentRightSlicePostFiber_comp (g : Y ⟶ Z) (h : Z ⟶ W) :
    coherentRightSlicePostFiber X g ≫ coherentRightSlicePostFiber X h =
      coherentRightSlicePostFiber X (g ≫ h) := by
  apply vertexFiber_hom_ext p(W) (coherentNerveVertex X)
  rw [Category.assoc, coherentRightSlicePostFiber_ι, ← Category.assoc,
    coherentRightSlicePostFiber_ι, coherentRightSlicePostFiber_ι,
    Category.assoc, coherentRightSlicePost_comp]

/-- 元の全 Hom 比較は、同じ fiber 上でも指定終域射の後合成と厳密に可換。 -/
lemma coherentHomSliceFiberComparison_post (g : Y ⟶ Z) :
    J(Y) ≫ coherentRightSlicePostFiber X g =
      (SSet.uliftFunctor.{v, u}).map (eHomWhiskerLeft SSet X g) ≫ J(Z) := by
  apply vertexFiber_hom_ext p(Z) (coherentNerveVertex X)
  simpa only [Category.assoc, coherentRightSlicePostFiber_ι] using
    (coherentHomSliceComparison_post (X := X) g)

end SerrePositivity.InfinityCategories.F2
