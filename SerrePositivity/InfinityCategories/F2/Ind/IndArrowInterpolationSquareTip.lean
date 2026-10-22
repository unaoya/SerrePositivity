module

public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowInterpolationSquare
public import SerrePositivity.InfinityCategories.F2.Ind.ArrowInterpolationTipLine

/-!
概要：帰還した全変換の終端側面は、元の指定 Ind 射図式全体そのもの。
方針：全円柱同型の逆の終端辺と、元の始点全錐の同じ全辺を回収する。
規約：元の区間図式の厳密な等式。使われ方：元の射図式への全余錐の curry。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {κ : Cardinal.{u}} {C A : SSet.{u}} [Quasicategory C]
  {D : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) ⟶ IndInfinity κ C}
  {q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ diagramComma κ D}
  (V : IndArrowInterpolationData κ D q)

/-- 貼り合わせた元の全錐の終端辺は、元の指定図式の同じ辺。 -/
lemma indArrowInterpolationGlue_tip :
    sliceOverUncurry (arrowInterpolationSourceTip
      ((SSet.uliftFunctor.{u + 1, u}).obj (join A (Δ[0] : SSet.{u}))) ≫
        indArrowInterpolationGlue V) = (joinStdSimplexIso 0 0).hom ≫
          (liftedIntervalToSmall.{u} ≫ D) := by
  let B := (SSet.uliftFunctor.{u + 1, u}).obj (join A (Δ[0] : SSet.{u}))
  have h := congrArg (fun f => joinInr B (Δ[0] : SSet.{u + 1}) ≫ f)
    (indArrowInterpolationGlue_source V)
  have h' : arrowInterpolationSourceTip B ≫ indArrowInterpolationGlue V =
      joinInr B Δ[0] ≫ indArrowSourceSliceLift κ D V.sourceCone := by
    simpa only [arrowInterpolationSourceTip, Category.assoc] using h
  exact (congrArg sliceOverUncurry h').trans (indArrowSourceSliceLift_tip κ D V.sourceCone)

/-- 帰還した全変換の終端側面は、元の指定 Ind 区間図式そのもの。 -/
lemma indArrowInterpolationSquare_tip :
    (joinInr ((SSet.uliftFunctor.{u + 1, u}).obj (join A (Δ[0] : SSet.{u}))) Δ[0] ▷ Δ[1]) ≫
      indArrowInterpolationSquare V =
        snd (Δ[0] : SSet.{u + 1}) Δ[1] ≫ (liftedIntervalToSmall.{u} ≫ D) := by
  let B := (SSet.uliftFunctor.{u + 1, u}).obj (join A (Δ[0] : SSet.{u}))
  have hi := congrArg (fun f => f ≫ sliceOverUncurry (indArrowInterpolationGlue V))
    (arrowInterpolationCoconeIso_inv_tip B)
  calc
    _ = arrowInterpolationTipLine B ≫ sliceOverUncurry (indArrowInterpolationGlue V) := by
      simpa only [indArrowInterpolationSquare, Category.assoc] using hi
    _ = snd (Δ[0] : SSet.{u + 1}) Δ[1] ≫ (joinStdSimplexIso 0 0).inv ≫
        sliceOverUncurry (arrowInterpolationSourceTip B ≫ indArrowInterpolationGlue V) := by
      simp only [arrowInterpolationTipLine, sliceOverUncurry_precomp, Category.assoc]
    _ = snd (Δ[0] : SSet.{u + 1}) Δ[1] ≫ (joinStdSimplexIso 0 0).inv ≫
        (joinStdSimplexIso 0 0).hom ≫ (liftedIntervalToSmall.{u} ≫ D) := by
      rw [indArrowInterpolationGlue_tip]
    _ = _ := by simp only [Iso.inv_hom_id_assoc]

end SerrePositivity.InfinityCategories.F2.Ind
