module
public import SerrePositivity.KST.SConstruction.ColimitComparison

/-! # 零対象だけからなる span の普遍余錐
概要：全入力が零対象なら、その普遍余錐の全頂点も零対象。
方針：定値零図式の普遍余錐と関手全体を同型で比較する。
規約：入力の零対象や零射を厳密に同じとは仮定しない。使われ方：gapped の零対角の閉性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：零対象だけの span の普遍余錐は関手圏の零対象。
方針：定値零四角形の余錐との関手同型を、図式の零対象性から構成する。
規約：安定性は不要。使われ方：完成した全頂点の零対象性。 -/
lemma zeroSpanColimit_functorVertex_isZero {C : SSet.{u}} [Quasicategory C] [HasZeroVertex C]
    {p : (horn 2 0 : SSet.{u}) ⟶ C} (c : JoinCocone p) (hc : IsColimitCone c)
    (hp : ∀ a : (horn 2 0 : SSet.{u}) _⦋0⦌, IsZeroVertex (p.app (Opposite.op ⦋0⦌) a)) :
    IsZeroVertex (functorVertex c.val) := by
  let z := chosenZeroVertex C
  let Z : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ C := SSet.const z.vertex
  have hZ : IsPushoutSquare Z := by
    have h := isPushoutSquare_fst (SSet.const z.vertex : (Δ[1] : SSet.{u}) ⟶ C)
    rwa [SSet.comp_const] at h
  have hpZ : IsZeroVertex (functorVertex (pushoutSpan Z)) := by
    change IsZeroVertex (functorVertex (spanSquareBoundary ≫ SSet.const z.vertex))
    rw [SSet.comp_const]
    exact functor_const_isZeroVertex z.vertex z.isZero
  have hpF := isZeroVertex_functorVertex_of_pointwise p hp
  let e : FunctorIso (pushoutSpan Z) p :=
    zeroVertexIso ⟨_, hpZ.1, hpZ.2⟩ ⟨_, hpF.1, hpF.2⟩
  let E := colimitCoconeIsoOfDiagramIso (pushoutCocone Z) c hZ hc e
  have hcz : IsZeroVertex (functorVertex (pushoutCocone Z).val) := by
    change IsZeroVertex (functorVertex (spanCoconeSquareIso.hom ≫ SSet.const z.vertex))
    rw [SSet.comp_const]
    exact functor_const_isZeroVertex z.vertex z.isZero
  exact hcz.of_vertexIso E

/-- 概要：零対象だけの span の普遍余錐の全頂点は零対象。
方針：余錐全体の関手の零対象性を各点で評価する。
規約：錐頂点も境界の全頂点も含む。使われ方：二方向補完の全行の零脚。 -/
lemma zeroSpanColimit_all_vertices_zero {C : SSet.{u}} [Quasicategory C] [HasZeroVertex C]
    {p : (horn 2 0 : SSet.{u}) ⟶ C} (c : JoinCocone p) (hc : IsColimitCone c)
    (hp : ∀ a : (horn 2 0 : SSet.{u}) _⦋0⦌, IsZeroVertex (p.app (Opposite.op ⦋0⦌) a))
    (v : (join (horn 2 0 : SSet.{u}) Δ[0]) _⦋0⦌) :
    IsZeroVertex (c.val.app (Opposite.op ⦋0⦌) v) := by
  have h := isZeroVertex_evaluateFunctorAt (zeroSpanColimit_functorVertex_isZero c hc hp) v
  rwa [evaluateFunctorAt_functorVertex] at h

end SerrePositivity.KST.SConstruction
