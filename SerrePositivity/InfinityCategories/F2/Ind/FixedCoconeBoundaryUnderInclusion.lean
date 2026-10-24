module

public import SerrePositivity.InfinityCategories.F2.Ind.FixedCoconeBoundaryUnder

/-!
概要：三条件固定の全余錐の包含と、元の三つの全固定条件を回収する。
方針：二つの実 fiber の包含を合成し、それぞれの定値射影を使う。
規約：全次数の底・終点・指定評価の余錐を保持する。
使われ方：同じ固定比較から、三条件を全時刻で保つ実円柱を取り出す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {A X Z : SSet.{u}} (p : (Δ[0] : SSet.{u}) ⟶ X) (b : A ⟶ X)
  (e : X ⟶ Z) (s : join A (Δ[0] : SSet.{u}) ⟶ Z)

/-- 概要：三条件固定の余錐の元の全関手空間への包含。
方針：二つの fiber 包含を合成。規約：固定条件を保持。使われ方：実円柱の回収。 -/
def fixedCoconeBoundaryUnderInclusion : fixedCoconeBoundaryUnder p b e s ⟶
    (ihom (join A (Δ[0] : SSet.{u}))).obj X :=
  vertexFiberι (fixedCoconeBoundaryInclusion p b ≫ (ihom (join A Δ[0])).map e)
    (functorVertex s) ≫ fixedCoconeBoundaryInclusion p b

/-- 概要：元の全底図式の固定条件。方針：内側の定値射影を使う。
規約：全係数を保持。使われ方：実円柱の底境界。 -/
lemma fixedCoconeBoundaryUnderInclusion_old : fixedCoconeBoundaryUnderInclusion p b e s ≫
    (pre (joinInl A (Δ[0] : SSet.{u}))).app X = SSet.const (functorVertex b) := by
  rw [fixedCoconeBoundaryUnderInclusion, Category.assoc,
    fixedCoconeBoundaryInclusion_old, SSet.comp_const]

/-- 概要：元の指定終点の固定条件。方針：内側の定値射影を使う。
規約：全係数を保持。使われ方：実円柱の終点境界。 -/
lemma fixedCoconeBoundaryUnderInclusion_tip : fixedCoconeBoundaryUnderInclusion p b e s ≫
    (pre (joinInr A (Δ[0] : SSet.{u}))).app X = SSet.const (functorVertex p) := by
  rw [fixedCoconeBoundaryUnderInclusion, Category.assoc,
    fixedCoconeBoundaryInclusion_tip, SSet.comp_const]

/-- 概要：元の指定評価後の全余錐の固定条件。方針：外側の定値射影を使う。
規約：全係数を保持。使われ方：実円柱の相対条件。 -/
lemma fixedCoconeBoundaryUnderInclusion_evaluation :
    fixedCoconeBoundaryUnderInclusion p b e s ≫ (ihom (join A Δ[0])).map e =
      SSet.const (functorVertex s) := by
  rw [fixedCoconeBoundaryUnderInclusion, Category.assoc, vertexFiberι_comp]

end SerrePositivity.InfinityCategories.F2.Ind
