module

public import SerrePositivity.InfinityCategories.Core.Cocone
public import SerrePositivity.InfinityCategories.Core.Terminal

/-!
概要：終対象への元の余錐を、部分形状上で全射を固定したまま延長する。
方針：終点 slice の trivial Kan な射影で元の単射に沿って持ち上げる。
規約：元の指定頂点と全余錐を保持し、形状の有限性を仮定しない。
使われ方：点追加の再構成で元の旧族の全円柱を厳密に固定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 概要：指定した終対象への部分余錐は、同じ頂点と全制限を保って延長できる。
方針：終点 slice への相対持ち上げ。規約：元の全射。使われ方：旧族を固定した再構成。 -/
lemma exists_relative_terminal_cocone {A B X : SSet.{u}} (i : A ⟶ B) [Mono i]
    (F : B ⟶ X) (t : X _⦋0⦌) (ht : IsTerminalVertex t)
    (c : JoinCocone (i ≫ F)) (hc : c.vertex = t) :
    ∃ d : JoinCocone F, d.vertex = t ∧
      joinMap i (𝟙 (Δ[0] : SSet.{u})) ≫ d.val = c.val := by
  have hp := (isTerminalVertex_iff_trivialKanFibration t).mp ht
  have : HasLiftingProperty i (sliceOverProjection (SSet.yonedaEquiv.symm t)) :=
    hp.mem i inferInstance
  have hfixed : joinInr A (Δ[0] : SSet.{u}) ≫ c.val = SSet.yonedaEquiv.symm t := by
    apply SSet.yonedaEquiv.injective
    rw [Equiv.apply_symm_apply]
    exact hc
  let a := sliceOverCurry c.val hfixed
  have ha : a ≫ sliceOverProjection (SSet.yonedaEquiv.symm t) = i ≫ F := by
    rw [sliceOverCurry_projection]
    exact c.property
  let sq : CommSq a i (sliceOverProjection (SSet.yonedaEquiv.symm t)) F := ⟨ha⟩
  let d : JoinCocone F := ⟨sliceOverUncurry sq.lift, by
    rw [sliceOverUncurry_projection, sq.fac_right]⟩
  refine ⟨d, ?_, ?_⟩
  · change SSet.yonedaEquiv (joinInr B (Δ[0] : SSet.{u}) ≫ sliceOverUncurry sq.lift) = t
    rw [sliceOverUncurry_fixed, Equiv.apply_symm_apply]
  · change joinMap i (𝟙 (Δ[0] : SSet.{u})) ≫ sliceOverUncurry sq.lift = c.val
    rw [← sliceOverUncurry_precomp, sq.fac_left, sliceOverUncurry_curry]

end SerrePositivity.InfinityCategories.F2.Ind
