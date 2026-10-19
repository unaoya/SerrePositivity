module

public import SerrePositivity.KST.Spectra.SkeletalTransitionLatchingPullback
public import Mathlib.CategoryTheory.Limits.Types.Pushouts

/-!
概要：標準単体の骨格間の包含は実際の Reedy 単射。
方針：latching の pullback 正方形を各次数で pushout に貼り、共通部分から比較射の単射性を得る。
規約：点ごとの単射性だけで済ませず、相対 latching 射そのものを調べる。
使われ方：Goerss–Jardine VIII §1。通常 Tot の有限段の塔の fibration 条件。
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits SSet
open SerrePositivity.Reedy
namespace SerrePositivity.KST.Spectra.SkeletalStandardLatching
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 標準単体の有限骨格の包含は実際の Reedy 単射。 -/
lemma transition_reedy_mono {n m : ℕ} (h : n ≤ m) :
    reedyLeft simplex (MorphismProperty.monomorphisms SSet.{u}) (transition.{u} h) := by
  intro j
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro k
  let E := (evaluation SimplexCategoryᵒᵖ (Type u)).obj k
  let θ := transition.{u} h
  let a := (latchingEvaluation simplex j).map θ
  let b := (latchingComparison simplex j).app (diagram.{u} n)
  let c := (latchingComparison simplex j).app (diagram.{u} m)
  let : Mono c := mono m j
  change Mono (E.map (relativeLatchingMap simplex j θ))
  refine Types.mono_of_isPushout_of_isPullback
    ((IsPushout.of_hasPushout a b).map E) (transition_latching_app_isPullback h j k) ?_ ?_ ?_
  · rw [← E.map_comp, inl_relativeLatchingMap]
    rfl
  · rw [← E.map_comp, inr_relativeLatchingMap]
    rfl
  · intro x y _ _ he
    exact Subtype.ext (congrArg
      (fun z : ((stdSimplex.{u}.obj j).skeleton m : SSet.{u}).obj k ↦ z.val) he)

end
end SerrePositivity.KST.Spectra.SkeletalStandardLatching
