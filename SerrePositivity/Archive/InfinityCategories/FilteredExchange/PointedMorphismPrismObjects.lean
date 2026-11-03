module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedReverseMorphismPrism
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceSimplexPointedFamilyCoordinates
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.InitialReverseThickeningCoordinates

/-!
概要：同じ固定射の二つの実 prism の全単体について、実対象を照合する。
方針：最初の頂点と正頂点に分け、同じ時刻ラベルの反転を計算する。
規約：元の初点係数を保持。使われ方：二つの実 prism の豊穣 Hom の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits

/-- 元の全単体の反転合成表示と初点固定表示は、全ての実対象で一致する。 -/
lemma pointedMorphismPrism_obj {K L : KanObject.{u}} (f : K ⟶ L) {n : ℕ}
    (t : (Δ[1] : SSet.{u + 1}) _⦋n⦌)
    (p : (SimplicialCategory.sHom pointKanObject K).op _⦋n⦌) (a : Fin (n + 2)) :
    coherentCompositionObj (Opposite.op L) (Opposite.op K) (Opposite.op pointKanObject)
      (stableReverseOrderHom (stdSimplex.objEquiv t).toOrderHom) a.rev =
    Opposite.op ((coneInitialFixedSimplex pointKanObject
      (fixedInitialSimplexReindex K (stdSimplex.objEquiv t)
        (⟨coherentConeTailExtension (coherentNerveEdge f).edge, rfl⟩ :
          fixedInitialSimplex K 1)) (SSet.yonedaEquiv.symm p)).obj ⟨ULift.up a⟩) := by
  induction a using Fin.cases with
  | zero =>
    rw [Fin.rev_zero, coherentCompositionObj_last]
    rfl
  | succ a =>
    rw [Fin.rev_succ]
    simp only [coherentCompositionObj, Fin.lastCases_castSucc,
      stableReverseOrderHom, OrderHom.coe_mk, Fin.rev_rev]
    have ht : (stdSimplex.objEquiv t).toOrderHom a = 0 ∨
        (stdSimplex.objEquiv t).toOrderHom a = 1 :=
      (by decide : ∀ z : Fin 2, z = 0 ∨ z = 1) _
    rcases ht with h | h
    · simp only [h, show (0 : Fin 2).rev = 1 from rfl,
        show ¬(1 : Fin 2) = 0 from by decide, ite_false]
      change Opposite.op K = Opposite.op ((ComposableArrows.mk₁ f).obj
        ((stdSimplex.objEquiv t).toOrderHom a))
      rw [h]
      rfl
    · simp only [h, show (1 : Fin 2).rev = 0 from rfl, ite_true]
      change Opposite.op L = Opposite.op ((ComposableArrows.mk₁ f).obj
        ((stdSimplex.objEquiv t).toOrderHom a))
      rw [h]
      rfl

end SerrePositivity.InfinityCategories.F2
