module
public import SerrePositivity.KST.LocalizingInvariants.PullbackFinalHornExtension

public import SerrePositivity.KST.LocalizingInvariants.FinalArrowCospanFamily
public import SerrePositivity.KST.LocalizingInvariants.IdentityArrowPullback
public import SerrePositivity.InfinityCategories.F1.Fibrations.CartesianEdge

/-!
概要：矢印圏の辺の実正方形が pullback なら、終点評価に対して cartesian。
方針：最終外ホーンを正方形族へ収縮し、末尾二点の普遍性で延長して底辺を回収する。
規約：任意の quasicategory に対する全最終外ホーン充填。使われ方：span の局所 cartesian 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma arrowTarget_isCartesianEdge_of_pullback {X : SSet.{u}} [Quasicategory X]
    (e : ((ihom (Δ[1] : SSet.{u})).obj X) _⦋1⦌)
    (he : IsPullbackSquare (uncurry (SSet.yonedaEquiv.symm e))) :
    IsCartesianEdge (evaluateFunctorAt (Y := X) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) e := by
  intro m σ β hσ sq
  let a := finalHornArrowSquares m σ
  let v := σ.app (Opposite.op ⦋0⦌) (finalHornLastVertex m)
  let d := finalArrowCospanFamily (m + 2) β v (finalHorn_lastArrow_target m σ β sq.w)
  have ha : a ≫ (pre cospanSquareBoundary).app X =
      (horn (m + 2) (Fin.last (m + 2))).ι ≫ d := finalHornArrowSquares_cospan m σ β sq.w
  have hprev : IsPullbackSquare ((functorVertexEquiv (Δ[1] ⊗ Δ[1] : SSet.{u}) X).symm
      (a.app (Opposite.op ⦋0⦌) (finalHornPenultimateVertex m))) := by
    dsimp only [a]
    rw [finalHornArrowSquares_penultimate, ← functorVertexEquiv_apply, Equiv.symm_apply_apply, hσ]
    exact he
  have hlast : IsPullbackSquare ((functorVertexEquiv (Δ[1] ⊗ Δ[1] : SSet.{u}) X).symm
      (a.app (Opposite.op ⦋0⦌) (finalHornLastVertex m))) := by
    dsimp only [a]
    rw [finalHornArrowSquares_last, ← functorVertexEquiv_apply, Equiv.symm_apply_apply]
    exact constantArrowFamily_isPullback _
  obtain ⟨F, hF, hFc⟩ := exists_finalHorn_squareFamily_extension m a d ha hprev hlast
  let G := F ≫ (pre squareBottomEdge).app X
  have hG : (horn (m + 2) (Fin.last (m + 2))).ι ≫ G = σ := by
    dsimp only [G]
    rw [← Category.assoc, hF]
    exact finalHornArrowSquares_bottom m σ
  have hp : (pre cospanSquareBoundary).app X ≫ (pre horn₂₂.ι₀₂).app X =
      (pre squareRightEdge).app X := by
    rw [← NatTrans.comp_app, ← pre_map, cospanSquareBoundary_rightEdge]
  have hv : (pre squareBottomEdge).app X ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      (pre squareRightEdge).app X ≫
        evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
    rw [stable_pre_evaluateFunctorAt, stable_pre_evaluateFunctorAt]
    rfl
  have hGp : G ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = β := by
    calc
      G ≫ evaluateFunctorAt _ = F ≫ (pre squareRightEdge).app X ≫
          evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
        dsimp only [G]
        rw [Category.assoc, hv]
      _ = (F ≫ (pre cospanSquareBoundary).app X) ≫ (pre horn₂₂.ι₀₂).app X ≫
          evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
        simpa only [Category.assoc] using
          (congrArg (fun k : (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X ⟶
              (ihom (Δ[1] : SSet.{u})).obj X =>
            F ≫ k ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) hp).symm
      _ = d ≫ (pre horn₂₂.ι₀₂).app X ≫
          evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by rw [hFc]
      _ = β := by
        simpa only [Category.assoc] using finalArrowCospanFamily_base (m + 2) β v
          (finalHorn_lastArrow_target m σ β sq.w)
  exact CommSq.HasLift.mk' { l := G, fac_left := hG, fac_right := hGp }

end SerrePositivity.KST.LocalizingInvariants
