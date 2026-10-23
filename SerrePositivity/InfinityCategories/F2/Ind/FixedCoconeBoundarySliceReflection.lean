module

public import SerrePositivity.InfinityCategories.F2.Ind.FixedCoconeBoundaryPost
public import SerrePositivity.InfinityCategories.Core.SliceFixedDiagramIso
public import SerrePositivity.InfinityCategories.F2.Ind.FullyFaithfulPullbackRight
public import SerrePositivity.InfinityCategories.F1.FullyFaithfulPostcomposition

/-!
概要：両境界固定の余錐の同型を、同じ元の slice 関手の同型として読む。
方針：実終点固定 fiber へ写し、既存の相対 join 円柱による反映を適用する。
規約：元の両端の全射を回収してから反映。使われ方：充満忠実な comma 射影での帰還。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {A X : SSet.{u}} (p : (Δ[0] : SSet.{u}) ⟶ X) (b : A ⟶ X)

/-- 同じ終点固定条件を保つ、両境界 fiber から元の終点 fiber への射。 -/
def fixedCoconeBoundaryToTip : fixedCoconeBoundary p b ⟶
    vertexFiber ((pre (joinInr A (Δ[0] : SSet.{u}))).app X) (functorVertex p) :=
  vertexFiberLift _ _ (fixedCoconeBoundaryInclusion p b)
    (fixedCoconeBoundaryInclusion_tip p b)

/-- 元の両全余錐の頂点を回収した固定境界同型は、同じ slice 関手の同型を与える。 -/
lemma nonempty_sliceFunctorIso_of_fixedCoconeBoundaryIso [Quasicategory X]
    (f g : A ⟶ sliceOver p) (v w : (fixedCoconeBoundary p b) _⦋0⦌)
    (hv : v.val = functorVertex (sliceOverUncurry f))
    (hw : w.val = functorVertex (sliceOverUncurry g)) (e : VertexIso v w) :
    Nonempty (FunctorIso f g) := by
  have hv' : (fixedCoconeBoundaryToTip p b).app (Opposite.op ⦋0⦌) v =
      sliceOverFixedDiagramVertex f := by
    apply Subtype.ext
    exact hv
  have hw' : (fixedCoconeBoundaryToTip p b).app (Opposite.op ⦋0⦌) w =
      sliceOverFixedDiagramVertex g := by
    apply Subtype.ext
    exact hw
  apply nonempty_functorIso_of_sliceOverFixedDiagramVertexIso f g
  simpa only [hv', hw'] using VertexIso.map e (fixedCoconeBoundaryToTip p b)

/-- 両全余錐を回収した固定境界同型を、充満忠実な射の実 comma の全族へ反映する。 -/
lemma nonempty_commaFunctorIso_of_fixedCoconeBoundaryIso
    [Quasicategory X] {C : SSet.{u}} [Quasicategory C]
    (δ : C ⟶ X) (hδ : IsFullyFaithful δ)
    (f g : A ⟶ CategoryTheory.Limits.pullback δ (sliceOverProjection p))
    (v w : (fixedCoconeBoundary p b) _⦋0⦌)
    (hv : v.val = functorVertex (sliceOverUncurry
      (f ≫ CategoryTheory.Limits.pullback.snd δ (sliceOverProjection p))))
    (hw : w.val = functorVertex (sliceOverUncurry
      (g ≫ CategoryTheory.Limits.pullback.snd δ (sliceOverProjection p))))
    (e : VertexIso v w) : Nonempty (FunctorIso f g) := by
  obtain ⟨e'⟩ := nonempty_sliceFunctorIso_of_fixedCoconeBoundaryIso p b
    (f ≫ CategoryTheory.Limits.pullback.snd δ (sliceOverProjection p))
    (g ≫ CategoryTheory.Limits.pullback.snd δ (sliceOverProjection p)) v w hv hw e
  have hf := fullyFaithful_pullback_snd_of_innerFibration_right hδ (sliceOverProjection p)
  exact ⟨hf.preimageFunctorIso e'⟩

end SerrePositivity.InfinityCategories.F2.Ind
