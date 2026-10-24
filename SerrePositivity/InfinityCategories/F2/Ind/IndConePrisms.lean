module

public import SerrePositivity.InfinityCategories.F2.Ind.DiagramCommaRightPrism
public import SerrePositivity.InfinityCategories.Core.UniverseJoinSimplexShapes

/-!
概要：元の試験族 q と下方の元の余錐 G の全円柱を、同じ右余錐形状へそろえる。
方針：元の余錐形状の宇宙同型と、試験族・形状の全制限の自然性を使う。
規約：元の C 全図式、指定 D、旧族と下方全余錐を厳密に保持する。
使われ方：一般の二段 slice 持ち上げへ、元の図式 comma の全データを渡す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) {L C : SSet.{u}} [Quasicategory C]
  (D : (SSet.uliftFunctor.{u + 1, u}).obj (join L (Δ[0] : SSet.{u})) ⟶ IndInfinity κ C)
/-- 概要：元の q と下方余錐 G の全円柱と境界を、同じ宇宙表示で保持する。
方針：元の形状同型と全円柱の自然性。規約：全射の等号。使われ方：二段 slice 持ち上げ。 -/
def indConeNormalizedDiagram :
    join ((SSet.uliftFunctor.{u + 1, u}).obj L) (Δ[0] : SSet.{u + 1}) ⟶ IndInfinity κ C :=
  (uliftCoconeShapeIso.{u, u + 1} L 0).inv ≫ D
/-- 概要：元の q と下方余錐 G の全円柱と境界を、同じ宇宙表示で保持する。
方針：元の形状同型と全円柱の自然性。規約：全射の等号。使われ方：二段 slice 持ち上げ。 -/
lemma indConeNormalizedDiagram_inl :
    joinInl ((SSet.uliftFunctor.{u + 1, u}).obj L) (Δ[0] : SSet.{u + 1}) ≫
      indConeNormalizedDiagram κ D =
    (SSet.uliftFunctor.{u + 1, u}).map (joinInl L (Δ[0] : SSet.{u})) ≫ D := by
  rw [indConeNormalizedDiagram, ← Category.assoc, uliftCoconeShapeIso_inv_inl]
/-- 概要：元の正規化した全図式の同じ終点写像。
方針：元の右包含で制限。規約：全射を保持。使われ方：実終点 slice と comma の型。 -/
def indConeEndpointPoint : (Δ[0] : SSet.{u + 1}) ⟶ IndInfinity κ C :=
  joinInr ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0] ≫ indConeNormalizedDiagram κ D
variable {T : SSet.{u + 1}} (q : T ⟶ diagramComma κ D)
/-- 概要：元の q と下方余錐 G の全円柱と境界を、同じ宇宙表示で保持する。
方針：元の形状同型と全円柱の自然性。規約：全射の等号。使われ方：二段 slice 持ち上げ。 -/
def indConeOriginalPrism : join T (Δ[0] : SSet.{u + 1}) ⊗
    join ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0] ⟶ IndInfinity κ C :=
  (join T (Δ[0] : SSet.{u + 1}) ◁ (uliftCoconeShapeIso.{u, u + 1} L 0).inv) ≫
    diagramCommaRightPrism κ D q
/-- 概要：元の q と下方余錐 G の全円柱と境界を、同じ宇宙表示で保持する。
方針：元の形状同型と全円柱の自然性。規約：全射の等号。使われ方：二段 slice 持ち上げ。 -/
lemma indConeOriginalPrism_tip :
    (joinInr T (Δ[0] : SSet.{u + 1}) ▷ join ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0]) ≫
      indConeOriginalPrism κ D q = snd (Δ[0] : SSet.{u + 1})
        (join ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0]) ≫ indConeNormalizedDiagram κ D := by
  rw [indConeOriginalPrism, ← Category.assoc, ← whisker_exchange,
    Category.assoc, diagramCommaRightPrism_tip, ← Category.assoc, whiskerLeft_snd,
    Category.assoc]
  rfl
/-- 概要：元の q と下方余錐 G の全円柱と境界を、同じ宇宙表示で保持する。
方針：元の形状同型と全円柱の自然性。規約：全射の等号。使われ方：二段 slice 持ち上げ。 -/
lemma indConeOriginalPrism_lower :
    (join T (Δ[0] : SSet.{u + 1}) ◁
      joinInl ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0]) ≫ indConeOriginalPrism κ D q =
    diagramCommaRightPrism κ
      ((SSet.uliftFunctor.{u + 1, u}).map (joinInl L (Δ[0] : SSet.{u})) ≫ D)
      (q ≫ diagramCommaRestriction κ D (joinInl L Δ[0])) := by
  rw [indConeOriginalPrism, ← Category.assoc, ← whiskerLeft_comp,
    uliftCoconeShapeIso_inv_inl, diagramCommaRightPrism_restrict]
variable (G : JoinCocone (q ≫ diagramCommaRestriction κ D (joinInl L (Δ[0] : SSet.{u}))))
/-- 概要：元の q と下方余錐 G の全円柱と境界を、同じ宇宙表示で保持する。
方針：元の形状同型と全円柱の自然性。規約：全射の等号。使われ方：二段 slice 持ち上げ。 -/
def indConeLowerPrism : join (join T (Δ[0] : SSet.{u + 1})) Δ[0] ⊗
    (SSet.uliftFunctor.{u + 1, u}).obj L ⟶ IndInfinity κ C :=
  diagramCommaRightPrism κ ((SSet.uliftFunctor.{u + 1, u}).map (joinInl L Δ[0]) ≫ D) G.val
/-- 概要：元の q と下方余錐 G の全円柱と境界を、同じ宇宙表示で保持する。
方針：元の形状同型と全円柱の自然性。規約：全射の等号。使われ方：二段 slice 持ち上げ。 -/
lemma indConeLowerPrism_tip :
    (joinInr (join T (Δ[0] : SSet.{u + 1})) Δ[0] ▷
      (SSet.uliftFunctor.{u + 1, u}).obj L) ≫ indConeLowerPrism κ D q G =
    snd (Δ[0] : SSet.{u + 1}) ((SSet.uliftFunctor.{u + 1, u}).obj L) ≫
      joinInl ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0] ≫ indConeNormalizedDiagram κ D := by
  rw [indConeLowerPrism, diagramCommaRightPrism_tip, indConeNormalizedDiagram_inl]
/-- 概要：元の q と下方余錐 G の全円柱と境界を、同じ宇宙表示で保持する。
方針：元の形状同型と全円柱の自然性。規約：全射の等号。使われ方：二段 slice 持ち上げ。 -/
lemma indConeLowerPrism_old :
    (joinMap (joinInl T (Δ[0] : SSet.{u + 1})) (𝟙 Δ[0]) ▷
      (SSet.uliftFunctor.{u + 1, u}).obj L) ≫ indConeLowerPrism κ D q G =
    (join T (Δ[0] : SSet.{u + 1}) ◁
      joinInl ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0]) ≫ indConeOriginalPrism κ D q := by
  rw [indConeLowerPrism, diagramCommaRightPrism_precomp, G.property,
    indConeOriginalPrism_lower]

end SerrePositivity.InfinityCategories.F2.Ind
