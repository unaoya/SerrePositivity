module

public import SerrePositivity.InfinityCategories.F2.Ind.ArrowInterpolationCoconeCoordinates
public import SerrePositivity.InfinityCategories.Core.Slice

/-!
概要：一般の右余錐図式を、同じ終点 slice の標準切断へ持ち上げる。
方針：元の二重余錐の最後の二点を潰す全射を、slice の普遍性に渡す。
規約：元の全図式と余錐点を厳密に保持し、持ち上げの選択を加えない。
使われ方：有限半順序形状の点追加で終端側面を元の D に固定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {L X : SSet.{u}} (d : join L (Δ[0] : SSet.{u}) ⟶ X)
/-- 概要：折り畳んだ全余錐の終点は元の指定終点。
方針：折り畳みの右端公式。規約：全射の等号。使われ方：slice の固定条件。 -/
lemma coneTerminalSlice_fixed :
    joinInr (join L (Δ[0] : SSet.{u})) Δ[0] ≫ (arrowInterpolationConeFold L ≫ d) =
      joinInr L Δ[0] ≫ d := by
  rw [← Category.assoc, arrowInterpolationConeFold_inr]
/-- 概要：元の全右余錐図式を、その指定終点の slice へ移す標準切断。
方針：折り畳んだ全余錐を curry。規約：元の図式。使われ方：点追加の終端側面。 -/
def coneTerminalSliceSection :
    join L (Δ[0] : SSet.{u}) ⟶ sliceOver (joinInr L Δ[0] ≫ d) :=
  sliceOverCurry (arrowInterpolationConeFold L ≫ d) (coneTerminalSlice_fixed d)
/-- 概要：標準切断は元の全図式を厳密に被覆する。
方針：折り畳みの左端公式。規約：全射の等号。使われ方：元の D の回収。 -/
lemma coneTerminalSliceSection_projection :
    coneTerminalSliceSection d ≫ sliceOverProjection (joinInr L Δ[0] ≫ d) = d := by
  rw [coneTerminalSliceSection, sliceOverCurry_projection,
    ← Category.assoc, arrowInterpolationConeFold_inl, Category.id_comp]
/-- 概要：元の全切断の全余錐は、同じ二重余錐の折り畳み。
方針：curry の逆関係。規約：全射の等号。使われ方：元の全変換の固定。 -/
lemma coneTerminalSliceSection_uncurry :
    sliceOverUncurry (coneTerminalSliceSection d) = arrowInterpolationConeFold L ≫ d :=
  sliceOverUncurry_curry _ _

end SerrePositivity.InfinityCategories.F2.Ind
