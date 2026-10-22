module

public import SerrePositivity.InfinityCategories.F2.Ind.IntervalSliceConeBoundary
public import SerrePositivity.InfinityCategories.F2.Ind.LiftedIntervalEndpoints
public import SerrePositivity.InfinityCategories.F2.Ind.DiagramConePointUncurry

/-!
概要：元の Ind 射図式への全錐を、その終点 slice 内の始点余錐へ移す。
方針：元の区間を正規化して組み替え、元の点 comma の全錐比較で射影を照合。
規約：元の試験族の全境界を厳密に保持。使われ方：終点 comma の円柱族の始点条件。
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

/-- 元の全錐族を同じ元の区間の終点 slice 内へ持ち上げる。 -/
def indArrowSourceSliceLift : join T (Δ[0] : SSet.{u + 1}) ⟶
    sliceOver (stdSimplex.δ 0 ≫ (liftedIntervalToSmall.{u} ≫ D)) :=
  intervalSliceConeLift (liftedIntervalToSmall.{u} ≫ D)
    (H ≫ pullback.snd (indYoneda κ C) (sliceOverProjection D) ≫
      sliceOverRestrict D liftedIntervalToSmall)

/-- 持ち上げは同じ元の始点の全余錐を被覆する。 -/
lemma indArrowSourceSliceLift_projection : indArrowSourceSliceLift κ D H ≫
    sliceOverProjection (stdSimplex.δ 0 ≫ (liftedIntervalToSmall.{u} ≫ D)) =
      sliceOverUncurry (H ≫ pullback.snd (indYoneda κ C) (sliceOverProjection D) ≫
        sliceOverRestrict D (diagramShapePoint (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2)))) := by
  rw [indArrowSourceSliceLift, intervalSliceConeLift_projection]
  simp only [Category.assoc]
  rw [← sliceOverRestrict_comp]
  exact congrArg (fun i : (Δ[0] : SSet.{u + 1}) ⟶
    (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) =>
      sliceOverUncurry (H ≫ pullback.snd (indYoneda κ C) (sliceOverProjection D) ≫
        sliceOverRestrict D i)) liftedIntervalToSmall_first

/-- 元の試験族の始点制限を保つ全錐なら、持ち上げの底も元の標準全余錐そのもの。 -/
lemma indArrowSourceSliceLift_projection_of_initial
    (q : T ⟶ diagramComma κ D)
    (hH : H ≫ diagramConePointRestriction κ D (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2)) =
      q ≫ diagramCommaEvaluation κ D (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) :
    indArrowSourceSliceLift κ D H ≫
      sliceOverProjection (stdSimplex.δ 0 ≫ (liftedIntervalToSmall.{u} ≫ D)) =
        joinMap q (𝟙 (Δ[0] : SSet.{u + 1})) ≫ (diagramCommaCocone κ D).val ≫
          evaluateFunctorAt (ULift.up (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2))) := by
  rw [indArrowSourceSliceLift_projection,
    ← diagramConePointRestriction_uncurry κ D (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) H]
  have h := congrArg (fun f => sliceOverUncurry (f ≫
    pullback.snd (indYoneda κ C) (sliceOverProjection (SSet.yonedaEquiv.symm
      (D.app (Opposite.op ⦋0⦌) (ULift.up (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2)))))))) hH
  simp only [Category.assoc] at h
  rw [diagramCommaEvaluation_uncurry κ D (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) q] at h
  simpa only [diagramCommaCocone, ← Category.assoc, ← sliceOverUncurry_precomp] using h

/-- 元のパラメーターの制限は、この実 slice 持ち上げでも保たれる。 -/
lemma indArrowSourceSliceLift_precomp {T₀ : SSet.{u + 1}} (g : T₀ ⟶ T) :
    joinMap g (𝟙 (Δ[0] : SSet.{u + 1})) ≫ indArrowSourceSliceLift κ D H =
      indArrowSourceSliceLift κ D (g ≫ H) := by
  unfold indArrowSourceSliceLift
  rw [intervalSliceConeLift_precomp]
  simp only [Category.assoc]

/-- 元の全錐族側の包含では、元の C の図式の Yoneda 像を被覆する。 -/
lemma indArrowSourceSliceLift_old_projection :
    joinInl T (Δ[0] : SSet.{u + 1}) ≫ indArrowSourceSliceLift κ D H ≫
      sliceOverProjection (stdSimplex.δ 0 ≫ (liftedIntervalToSmall.{u} ≫ D)) =
        H ≫ pullback.fst (indYoneda κ C) (sliceOverProjection D) ≫ indYoneda κ C := by
  rw [indArrowSourceSliceLift_projection, sliceOverUncurry_projection]
  simp only [Category.assoc, HomotopyLimits.sliceOverRestrict_projection]
  rw [← pullback.condition]

/-- 余錐頂点上の全辺も、元の同じ指定区間図式を保持する。 -/
lemma indArrowSourceSliceLift_tip :
    sliceOverUncurry (joinInr T (Δ[0] : SSet.{u + 1}) ≫ indArrowSourceSliceLift κ D H) =
      (joinStdSimplexIso 0 0).hom ≫ (liftedIntervalToSmall.{u} ≫ D) :=
  intervalSliceConeLift_tip _ _

end SerrePositivity.InfinityCategories.F2.Ind
