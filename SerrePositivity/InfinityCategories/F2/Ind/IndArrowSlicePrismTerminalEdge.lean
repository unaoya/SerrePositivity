module

public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowSlicePrismCone
public import SerrePositivity.InfinityCategories.F2.Ind.ArrowInterpolationTipTriangle
public import SerrePositivity.InfinityCategories.F2.Ind.ConePointSliceLift
public import SerrePositivity.InfinityCategories.F2.Ind.ConeMapRightAnodyne

/-!
概要：元の実 slice 円柱と標準持ち上げは、同じ全終端辺で厳密に一致する。
方針：sourceTip の三角形の二座標と元の終端側面を回収する。
規約：終点一点でなく元の区間全体を保持。使われ方：終端辺を固定した相対同型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

instance arrowInterpolationSourceTip_mono (A : SSet.{u}) :
    Mono (arrowInterpolationSourceTip A) := by
  rw [NatTrans.mono_iff_mono_app]
  rintro ⟨⟨n⟩⟩
  rw [mono_iff_injective]
  intro x y _
  apply SSet.stdSimplex.ext
  intro j
  apply Fin.ext
  have hx := (x j).isLt
  have hy := (y j).isLt
  omega

/-- sourceTip から新終点までの同じ全辺の包含は right anodyne。 -/
lemma arrowInterpolationTerminalEdge_rightAnodyne (A : SSet.{u}) :
    rightAnodyneExtensions (joinMap (arrowInterpolationSourceTip A) (𝟙 (Δ[0] : SSet.{u}))) :=
  coneMap_rightAnodyne (arrowInterpolationSourceTip A)

variable {κ : Cardinal.{u}} {C : SSet.{u}} [Quasicategory C]
  {D : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) ⟶ IndInfinity κ C}
  {T : SSet.{u + 1}} {q : T ⟶ diagramComma κ D}
  {H : T ⟶ pullback (indYoneda κ C) (sliceOverProjection D)}
  (W : IndArrowSlicePrism κ D q H)

/-- 元の実円柱は、全終端辺で同じ区間の標準 slice 切断そのもの。 -/
lemma indArrowSlicePrismCone_terminalEdge :
    joinMap (arrowInterpolationSourceTip T) (𝟙 Δ[0]) ≫ indArrowSlicePrismCone W =
      (joinStdSimplexIso 0 0).hom ≫
        intervalTerminalSliceSection (liftedIntervalToSmall.{u} ≫ D) := by
  let g := lift (stableLastJoinEvaluation 0) (joinStdSimplexIso.{u + 1} 0 0).hom
  have hg : g ≫ (joinInr T (Δ[0] : SSet.{u + 1}) ▷ Δ[1]) =
      lift (stableLastJoinEvaluation 0 ≫ joinInr T Δ[0]) (joinStdSimplexIso 0 0).hom := by rfl
  have hi := congrArg (fun f => f ≫ W.val) (arrowInterpolationSourceTip_triangle T)
  have hn := congrArg (fun f => f ≫ W.val) hg.symm
  have ht := congrArg (fun f => g ≫ f) W.tip
  calc
    _ = lift (stableLastJoinEvaluation 0 ≫ joinInr T Δ[0]) (joinStdSimplexIso 0 0).hom ≫
        W.val := by simpa only [indArrowSlicePrismCone, Category.assoc] using hi
    _ = g ≫ (joinInr T Δ[0] ▷ Δ[1]) ≫ W.val := by
      simpa only [Category.assoc] using hn
    _ = g ≫ snd Δ[0] Δ[1] ≫
        intervalTerminalSliceSection (liftedIntervalToSmall.{u} ≫ D) := by
      simpa only [Category.assoc] using ht
    _ = _ := by
      simpa only [g, Category.assoc] using congrArg
        (fun f => f ≫ intervalTerminalSliceSection (liftedIntervalToSmall.{u} ≫ D))
          (lift_snd (stableLastJoinEvaluation 0) (joinStdSimplexIso.{u + 1} 0 0).hom)

include W in
/-- 元の全底円柱も、全終端辺で同じ元の区間図式 D を回収する。 -/
lemma indArrowSlicePrismBaseCone_terminalEdge :
    joinMap (arrowInterpolationSourceTip T) (𝟙 Δ[0]) ≫ indArrowSlicePrismBaseCone (q := q) =
      (joinStdSimplexIso 0 0).hom ≫ (liftedIntervalToSmall.{u} ≫ D) := by
  have h := congrArg (fun f => f ≫ sliceOverProjection
    (stdSimplex.δ 0 ≫ (liftedIntervalToSmall.{u} ≫ D))) (indArrowSlicePrismCone_terminalEdge W)
  simpa only [Category.assoc, indArrowSlicePrismCone_projection,
    intervalTerminalSliceSection_projection] using h

/-- 標準持ち上げも、同じ元の全終端辺を厳密に回収する。 -/
lemma indArrowSlicePrismStandard_terminalEdge :
    joinMap (arrowInterpolationSourceTip T) (𝟙 Δ[0]) ≫
      conePointSliceLift (stdSimplex.δ 0 ≫ (liftedIntervalToSmall.{u} ≫ D))
        (indArrowSlicePrismBaseCone (q := q)) (indArrowSlicePrismBaseCone_fixed W) =
      (joinStdSimplexIso 0 0).hom ≫
        intervalTerminalSliceSection (liftedIntervalToSmall.{u} ≫ D) :=
  conePointSliceLift_edge _ _ _ _ (indArrowSlicePrismBaseCone_terminalEdge W)

end SerrePositivity.InfinityCategories.F2.Ind
