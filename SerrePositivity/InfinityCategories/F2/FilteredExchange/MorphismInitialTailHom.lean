module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.OrderDiagramHomLabels

/-!
概要：元の初点固定 tail の実 Hom を、同じ射の二時刻表示で正規化する。
方針：指定前合成の実ラベルを明示し、順序図式の端点移送式を適用する。
規約：元の path 全体と元の射を保持。使われ方：二つの実 prism の Hom の照合。
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

/-- 元の初点固定 tail の実頂点を、同じ元の射の二時刻へ送る順序写像。 -/
def morphismInitialTailOrder {n : ℕ} (α : ⦋n⦌ ⟶ ⦋1⦌) :
    ULift.{u} (Fin (n + 2)) →o Fin 2 :=
  (⟨ULift.down, fun _ _ h ↦ h⟩ : ULift.{u} (Fin 2) →o Fin 2).comp
    ((OrderHom.uliftMap.{0, 0, u, u} (coherentTailRetraction 1)).comp
      (OrderHom.uliftMap.{0, 0, u, u} (prependOrderHom α.toOrderHom)))

/-- 元の実初点は元の射の始域時刻に写る。 -/
lemma morphismInitialTailOrder_zero {n : ℕ} (α : ⦋n⦌ ⟶ ⦋1⦌) :
    morphismInitialTailOrder.{u} α (ULift.up 0) = 0 := rfl

/-- 元の正頂点のラベルは元の時刻パラメータそのもの。 -/
lemma morphismInitialTailOrder_succ {n : ℕ} (α : ⦋n⦌ ⟶ ⦋1⦌) (i : Fin (n + 1)) :
    morphismInitialTailOrder.{u} α (ULift.up i.succ) = α.toOrderHom i := rfl

/-- 元の実 tail の正規化した Hom は、同じ通常射の同じ順序射の頂点への定値射。 -/
lemma morphismInitialTail_map_labels {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y : C} (f : X ⟶ Y) {n : ℕ} (α : ⦋n⦌ ⟶ ⦋1⦌)
    (i j : ULift.{u} (Fin (n + 2))) (hij : i ≤ j) (k l : Fin 2)
    (hk : morphismInitialTailOrder α i = k) (hl : morphismInitialTailOrder α j = l)
    (hkl : k ≤ l) :
    (morphismInitialTail f α).val.map ⟨i⟩ ⟨j⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (congrArg (ComposableArrows.mk₁ f).obj hk)
        (congrArg (ComposableArrows.mk₁ f).obj hl)) =
      SSet.const (SimplicialCategory.homEquiv' _ _
        ((ComposableArrows.mk₁ f).map (homOfLE hkl))) := by
  change orderDiagramEnrichedHom
    ((morphismInitialTailOrder α).toFunctor ⋙ ComposableArrows.mk₁ f) ⟨i⟩ ⟨j⟩ ≫ _ = _
  exact orderDiagramEnrichedHom_label_transport
    (morphismInitialTailOrder α) (ComposableArrows.mk₁ f) ⟨i⟩ ⟨j⟩ hij k l hk hl hkl

end SerrePositivity.InfinityCategories.F2
