module

public import SerrePositivity.InfinityCategories.F2.Ind.ConeTerminalSliceLift
public import SerrePositivity.InfinityCategories.F2.Ind.ConePointSliceLift

/-!
概要：同じ終点への標準 slice 持ち上げは、元の試験形状の任意の制限を厳密に保持する。
方針：元の二重余錐の折り畳みの自然性を、そのまま slice の curry へ移す。
規約：元の全底余錐と固定終点を保持する。
使われ方：元の終点比較を旧族へ制限したときの、同じ比較同型の回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
/-- 概要：同じ終点への標準 slice 持ち上げは試験形状の全制限と厳密に可換。
方針：元の折り畳みの自然性。規約：全射の等号。使われ方：比較同型の旧族制限。 -/
lemma coneTerminalSliceLift_precomp {A A₀ X : SSet.{u}} (x : X _⦋0⦌)
    (b : join A (Δ[0] : SSet.{u}) ⟶ X) (hb : joinInr A Δ[0] ≫ b = SSet.yonedaEquiv.symm x)
    (f : A₀ ⟶ A) :
    joinMap f (𝟙 (Δ[0] : SSet.{u})) ≫ coneTerminalSliceLift x b hb =
    coneTerminalSliceLift x (joinMap f (𝟙 (Δ[0] : SSet.{u})) ≫ b)
      (by rw [← Category.assoc, joinInr_joinMap, Category.id_comp]; exact hb) := by
  apply sliceOverUncurry_injective
  rw [sliceOverUncurry_precomp, coneTerminalSliceLift, coneTerminalSliceLift,
    sliceOverUncurry_curry, sliceOverUncurry_curry, ← Category.assoc,
    arrowInterpolationConeFold_naturality, Category.assoc]
/-- 概要：元の任意の点写像の標準 slice 持ち上げも、全制限を厳密に保持する。
方針：同じ折り畳みの自然性。規約：元の点と全底余錐。使われ方：実終点比較の旧族制限。 -/
lemma conePointSliceLift_precomp {A A₀ X : SSet.{u}} (p : (Δ[0] : SSet.{u}) ⟶ X)
    (b : join A (Δ[0] : SSet.{u}) ⟶ X) (hb : joinInr A Δ[0] ≫ b = p) (f : A₀ ⟶ A) :
    joinMap f (𝟙 (Δ[0] : SSet.{u})) ≫ conePointSliceLift p b hb =
    conePointSliceLift p (joinMap f (𝟙 (Δ[0] : SSet.{u})) ≫ b)
      (by rw [← Category.assoc, joinInr_joinMap, Category.id_comp]; exact hb) := by
  apply sliceOverUncurry_injective
  rw [sliceOverUncurry_precomp, conePointSliceLift, conePointSliceLift,
    sliceOverUncurry_curry, sliceOverUncurry_curry, ← Category.assoc,
    arrowInterpolationConeFold_naturality, Category.assoc]
end SerrePositivity.InfinityCategories.F2.Ind
