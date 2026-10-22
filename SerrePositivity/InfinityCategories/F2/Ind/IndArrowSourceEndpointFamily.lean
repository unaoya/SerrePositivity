module

public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowSourceSliceLift
public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowEndpointCommaIso

/-!
概要：元の始点全錐族から、同じ C 側の図式を持つ終点 comma の族を構成する。
方針：全錐の組み替えの元の族側を取り、厳密な引き戻しと終点表示変更を使う。
規約：全パラメーター制限と C 射影を保持。使われ方：F と貼る始点余錐 G。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]
  (D : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) ⟶ IndInfinity κ C)
  {T : SSet.{u + 1}} (H : T ⟶ pullback (indYoneda κ C) (sliceOverProjection D))

/-- 元の C 図式と組み替えた全錐の元の族側から、終点の実引き戻しを作る。 -/
def indArrowSourceEndpointRaw : T ⟶ pullback (indYoneda κ C)
    (sliceOverProjection (stdSimplex.δ 0 ≫ (liftedIntervalToSmall.{u} ≫ D))) :=
  pullback.lift (H ≫ pullback.fst (indYoneda κ C) (sliceOverProjection D))
    (joinInl T (Δ[0] : SSet.{u + 1}) ≫ indArrowSourceSliceLift κ D H)
    (by simpa only [Category.assoc] using (indArrowSourceSliceLift_old_projection κ D H).symm)

/-- この実引き戻しは元の C 側の全族を保持。 -/
lemma indArrowSourceEndpointRaw_projection : indArrowSourceEndpointRaw κ D H ≫
    pullback.fst (indYoneda κ C)
      (sliceOverProjection (stdSimplex.δ 0 ≫ (liftedIntervalToSmall.{u} ≫ D))) =
        H ≫ pullback.fst (indYoneda κ C) (sliceOverProjection D) := pullback.lift_fst _ _ _

/-- この実引き戻しは組み替えた全錐の同じ族側を保持。 -/
lemma indArrowSourceEndpointRaw_slice : indArrowSourceEndpointRaw κ D H ≫
    pullback.snd (indYoneda κ C)
      (sliceOverProjection (stdSimplex.δ 0 ≫ (liftedIntervalToSmall.{u} ≫ D))) =
        joinInl T (Δ[0] : SSet.{u + 1}) ≫ indArrowSourceSliceLift κ D H :=
  pullback.lift_snd _ _ _

/-- 元の族の任意のパラメーター制限は、この実引き戻しで厳密に保たれる。 -/
lemma indArrowSourceEndpointRaw_precomp {T₀ : SSet.{u + 1}} (g : T₀ ⟶ T) :
    g ≫ indArrowSourceEndpointRaw κ D H = indArrowSourceEndpointRaw κ D (g ≫ H) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, indArrowSourceEndpointRaw_projection]
  · simp only [Category.assoc, indArrowSourceEndpointRaw_slice]
    have h := congrArg (fun f => joinInl T₀ (Δ[0] : SSet.{u + 1}) ≫ f)
      (indArrowSourceSliceLift_precomp κ D H g)
    calc
      _ = joinInl T₀ (Δ[0] : SSet.{u + 1}) ≫ joinMap g (𝟙 Δ[0]) ≫
          indArrowSourceSliceLift κ D H := by
        simpa only [Category.assoc] using (congrArg (fun f => f ≫
          indArrowSourceSliceLift κ D H) (joinInl_joinMap g (𝟙 (Δ[0] : SSet.{u + 1})))).symm
      _ = _ := h

/-- 元の同じ評価終点の comma 内の族へ戻す。 -/
def indArrowSourceEndpointFamily : T ⟶ leftKanShape (indYoneda κ C)
    (D.app (Opposite.op ⦋0⦌) (ULift.up (stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2)))) :=
  indArrowSourceEndpointRaw κ D H ≫ (indArrowEndpointCommaIso κ D).hom

/-- 終点の表示を戻しても、元の C 全図式は厳密に保たれる。 -/
lemma indArrowSourceEndpointFamily_projection : indArrowSourceEndpointFamily κ D H ≫
    leftKanProjection (indYoneda κ C)
      (D.app (Opposite.op ⦋0⦌) (ULift.up (stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2)))) =
        H ≫ pullback.fst (indYoneda κ C) (sliceOverProjection D) := by
  rw [indArrowSourceEndpointFamily, Category.assoc, indArrowEndpointCommaIso_projection,
    indArrowSourceEndpointRaw_projection]

/-- 元の評価終点の comma に戻した全族も、パラメーターの制限を厳密に保つ。 -/
lemma indArrowSourceEndpointFamily_precomp {T₀ : SSet.{u + 1}} (g : T₀ ⟶ T) :
    g ≫ indArrowSourceEndpointFamily κ D H = indArrowSourceEndpointFamily κ D (g ≫ H) := by
  simpa only [indArrowSourceEndpointFamily, Category.assoc] using congrArg
    (fun f => f ≫ (indArrowEndpointCommaIso κ D).hom) (indArrowSourceEndpointRaw_precomp κ D H g)

end SerrePositivity.InfinityCategories.F2.Ind
