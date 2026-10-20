module

public import SerrePositivity.InfinityCategories.F1.PointedRightNativeEvaluation

/-!
概要：元の coherent 右 Hom 全体で、pointed 輸送と Kan 空間の点評価を比較する。
方針：標準 Hom 比較の同じ逆と往復の関手同型を使って全パラメーターを降下する。
規約：元の coherentHomEquivalence の逆を保持する。
使われ方：既存の relativeHomCoherentRecovery と実際の pointed recovery の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- coherent な右 Hom の点評価は、元の標準 Hom 比較の逆を通す Kan の点評価と同型。 -/
def pointedRightHomEvaluate_nativeIso (K L : KanObject.{u})
    (s : (vertexFiber pointedSpaceProjection (spaceInfinityVertex K)) _⦋0⦌) :
    FunctorIso (pointedRightHomEvaluate K L s)
      ((coherentHomEquivalence K L).inv ≫
        (SSet.uliftFunctor.{u + 1, u}).map
          (evaluateFunctorAt (pointedSpaceFiberVertexEquiv K s)) ≫
        pointedRightFiberComparison L) := by
  have h : coherentHomComparison K L ≫ pointedRightHomEvaluate K L s =
      diagonalFiberTransport pointedSpaceProjection (SSet.const s)
        (coherentKanRightHomInterval K L) := by
    rw [pointedRightHomEvaluate, diagonalFiberTransport_precomp, SSet.comp_const]
    rfl
  have n := pointedRightNativeEvaluationIso K L s
  rw [← h] at n
  let e := coherentHomEquivalence K L
  have he : e.hom = coherentHomComparison K L := rfl
  have i := (e.invHomIso.postcomp (pointedRightHomEvaluate K L s)).symm
  have j := n.precomp e.inv
  rw [← he] at j
  exact (show FunctorIso (pointedRightHomEvaluate K L s)
    (e.inv ≫ e.hom ≫ pointedRightHomEvaluate K L s) from
      by simpa only [Category.assoc, Category.id_comp] using i) ≪≫ j

end SerrePositivity.InfinityCategories
