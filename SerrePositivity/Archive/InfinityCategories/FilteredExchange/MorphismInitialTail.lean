module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedMorphismPrismObjects
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.HomConstantTransport

/-!
概要：固定射 prism の元の初点固定 tail を、同じ通常射の順序図式で読む。
方針：実際の二つの添字前合成を保ち、既存の順序図式との可換性を使う。
規約：全係数の初点を固定。使われ方：実 prism の Hom の全単体照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {C : Type v} [Category.{u} C] [SimplicialCategory C] {X Y : C}

/-- 元の射の初点固定拡張を、同じ時刻ラベルで制限した元の tail。 -/
def morphismInitialTail (f : X ⟶ Y) {n : ℕ} (α : ⦋n⦌ ⟶ ⦋1⦌) :
    fixedInitialSimplex X n :=
  fixedInitialSimplexReindex X α
    (⟨coherentConeTailExtension (coherentNerveEdge f).edge, rfl⟩ : fixedInitialSimplex X 1)

/-- 同じ tail は、元の射の順序図式の二つの指定前合成そのもの。 -/
lemma morphismInitialTail_eq_order (f : X ⟶ Y) {n : ℕ} (α : ⦋n⦌ ⟶ ⦋1⦌) :
    (morphismInitialTail f α).val = enrichedFunctorOfOrderDiagram
      ((prependOrderHom α.toOrderHom).uliftMap.toFunctor ⋙
        (coherentTailRetraction 1).uliftMap.toFunctor ⋙
        (⟨ULift.down, fun _ _ h ↦ h⟩ : ULift.{u} (Fin 2) →o Fin 2).toFunctor ⋙
        ComposableArrows.mk₁ f) := by
  change (SimplicialThickening.functor _).comp SSet
    ((SimplicialThickening.functor _).comp SSet (enrichedFunctorOfOrderDiagram _)) = _
  rw [enrichedFunctorOfOrderDiagram_precomp, enrichedFunctorOfOrderDiagram_precomp]
  rfl

/-- 元の零ラベルの正頂点は、元の始域対象。 -/
lemma morphismInitialTail_obj_zero (f : X ⟶ Y) {n : ℕ} (α : ⦋n⦌ ⟶ ⦋1⦌)
    (j : Fin (n + 1)) (hj : α.toOrderHom j = 0) :
    (morphismInitialTail f α).val.obj ⟨ULift.up j.succ⟩ = X := by
  change (ComposableArrows.mk₁ f).obj (α.toOrderHom j) = X
  rw [hj]
  rfl

/-- 元の一ラベルの正頂点は、元の終域対象。 -/
lemma morphismInitialTail_obj_one (f : X ⟶ Y) {n : ℕ} (α : ⦋n⦌ ⟶ ⦋1⦌)
    (j : Fin (n + 1)) (hj : α.toOrderHom j = 1) :
    (morphismInitialTail f α).val.obj ⟨ULift.up j.succ⟩ = Y := by
  change (ComposableArrows.mk₁ f).obj (α.toOrderHom j) = Y
  rw [hj]
  rfl

end SerrePositivity.InfinityCategories.F2
