module

public import SerrePositivity.InfinityCategories.F2.Ind.IndConeSliceInterpolationData

/-!
概要：元の q と下方余錐 G の二段持ち上げを、同じ終点上の実 comma の全族へ移す。
方針：元の C 全図式と、構成した同じ slice の全射を厳密に引き戻す。
規約：元の全係数と全円柱を保持し、終点の表示変更はまだ行わない。
使われ方：一般の余錐積への実拡張に渡す、互換な二つの全境界の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {κ : Cardinal.{u}} {L C : SSet.{u}} [Quasicategory C]
  {D : (SSet.uliftFunctor.{u + 1, u}).obj (join L (Δ[0] : SSet.{u})) ⟶ IndInfinity κ C}
  {T : SSet.{u + 1}} {q : T ⟶ diagramComma κ D}
  {G : JoinCocone (q ≫ diagramCommaRestriction κ D (joinInl L (Δ[0] : SSet.{u})))}
  (V : IndConeSliceInterpolationData κ D q G)

/-- 概要：元の q の C 全図式と同じ全円柱を実終点 comma へ移す。
方針：元の両射を引き戻す。規約：全係数を保持。使われ方：補間の旧族側の境界。 -/
def indConeEndpointRaw : T ⊗ join ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0] ⟶
    pullback (indYoneda κ C) (sliceOverProjection (indConeEndpointPoint κ D)) :=
  pullback.lift
    ((T ◁ (uliftCoconeShapeIso.{u, u + 1} L 0).inv) ≫ diagramCommaOriginalFamily κ D q)
    ((joinInl T (Δ[0] : SSet.{u + 1}) ▷
      join ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0]) ≫ V.prism) (by
      have hb : (joinInl T (Δ[0] : SSet.{u + 1}) ▷
          join ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0]) ≫ indConeOriginalPrism κ D q =
          ((T ◁ (uliftCoconeShapeIso.{u, u + 1} L 0).inv) ≫
            diagramCommaOriginalFamily κ D q) ≫ indYoneda κ C := by
        rw [indConeOriginalPrism, ← Category.assoc, ← whisker_exchange,
          Category.assoc, diagramCommaRightPrism_old, Category.assoc]
      symm
      rw [Category.assoc, V.projection]
      exact hb)

/-- 概要：元の下方余錐 G の C 全図式と同じ全余錐を実終点 comma へ移す。
方針：元の両射を引き戻す。規約：全係数を保持。使われ方：補間の下方側の境界。 -/
def indConeLowerEndpointRaw : join T (Δ[0] : SSet.{u + 1}) ⊗
    (SSet.uliftFunctor.{u + 1, u}).obj L ⟶
      pullback (indYoneda κ C) (sliceOverProjection (indConeEndpointPoint κ D)) :=
  pullback.lift
    (diagramCommaOriginalFamily κ
      ((SSet.uliftFunctor.{u + 1, u}).map (joinInl L (Δ[0] : SSet.{u})) ≫ D) G.val)
    ((joinInl (join T (Δ[0] : SSet.{u + 1})) Δ[0] ▷
      (SSet.uliftFunctor.{u + 1, u}).obj L) ≫ V.lower) (by
      symm
      rw [Category.assoc, V.lower_projection, indConeLowerPrism, diagramCommaRightPrism_old])

/-- 概要：元の q の C 全図式を厳密に回収する。
方針：引き戻しの第一射影。規約：全係数を保持。使われ方：元の全図式への帰還。 -/
lemma indConeEndpointRaw_projection : indConeEndpointRaw V ≫
    pullback.fst (indYoneda κ C) (sliceOverProjection (indConeEndpointPoint κ D)) =
      (T ◁ (uliftCoconeShapeIso.{u, u + 1} L 0).inv) ≫ diagramCommaOriginalFamily κ D q :=
  pullback.lift_fst _ _ _
/-- 概要：元の全 slice 円柱の旧族側を厳密に回収する。
方針：引き戻しの第二射影。規約：全射を保持。使われ方：全境界の照合。 -/
lemma indConeEndpointRaw_slice : indConeEndpointRaw V ≫
    pullback.snd (indYoneda κ C) (sliceOverProjection (indConeEndpointPoint κ D)) =
      (joinInl T (Δ[0] : SSet.{u + 1}) ▷
        join ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0]) ≫ V.prism :=
  pullback.lift_snd _ _ _
/-- 概要：元の下方余錐 G の C 全図式を厳密に回収する。
方針：引き戻しの第一射影。規約：全係数を保持。使われ方：下方全図式への帰還。 -/
lemma indConeLowerEndpointRaw_projection : indConeLowerEndpointRaw V ≫
    pullback.fst (indYoneda κ C) (sliceOverProjection (indConeEndpointPoint κ D)) =
      diagramCommaOriginalFamily κ
        ((SSet.uliftFunctor.{u + 1, u}).map (joinInl L (Δ[0] : SSet.{u})) ≫ D) G.val :=
  pullback.lift_fst _ _ _
/-- 概要：元の下方全 slice 余錐の同じ源側を厳密に回収する。
方針：引き戻しの第二射影。規約：全射を保持。使われ方：元の全余錐の照合。 -/
lemma indConeLowerEndpointRaw_slice : indConeLowerEndpointRaw V ≫
    pullback.snd (indYoneda κ C) (sliceOverProjection (indConeEndpointPoint κ D)) =
      (joinInl (join T (Δ[0] : SSet.{u + 1})) Δ[0] ▷
        (SSet.uliftFunctor.{u + 1, u}).obj L) ≫ V.lower :=
  pullback.lift_snd _ _ _

end SerrePositivity.InfinityCategories.F2.Ind
