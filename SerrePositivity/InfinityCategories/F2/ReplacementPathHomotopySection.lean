module

public import SerrePositivity.InfinityCategories.F2.ReplacementPathHomotopy

/-!
概要：path 置換の切断による指定 lift の定値化。
方針：全部分複体の包含で比較して引き戻しの切断の式を使う。
規約：指定された三角形と同型の値を保持する。
使われ方：引き戻し錐と指定 path の比較を簡約する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

variable {X Y : SSet.{u}}
/-- 概要：path 置換の切断による指定 lift の定値化。
方針：全部分複体の包含で比較して引き戻しの切断の式を使う。
規約：元の指定ホモトピーと同型を変更しない。
使われ方：native な錐の可換性と指定 path の最終整合。 -/
lemma replacementPathHomotopy_lift (f : X ⟶ Y) :
    equivalenceHomotopyPathLift (replacementPathHomotopy f)
        (replacementPathHomotopy_invertible f) =
      pullback.fst (equivalencePathEndpoint Y 0) f := by
  apply (cancel_mono (fullSubcomplexOnVertices
    ((ihom (Δ[1] : SSet.{u})).obj Y) IsEquivalencePathVertex).ι).1
  exact (equivalenceHomotopyPathLift_ι _ _).trans (curry_uncurry _)
/-- 概要：path 置換の切断による指定 lift の定値化。
方針：全部分複体の包含で比較して引き戻しの切断の式を使う。
規約：元の指定ホモトピーと同型を変更しない。
使われ方：native な錐の可換性と指定 path の最終整合。 -/
lemma replacementPathHomotopy_section (f : X ⟶ Y) :
    equivalencePathReplacementSection f ≫
        equivalenceHomotopyPathLift (replacementPathHomotopy f)
          (replacementPathHomotopy_invertible f) =
      equivalencePathReplacementSection f ≫
        ((prismEndpoint 0 (equivalencePathReplacement f) ≫ replacementPathHomotopy f) ≫
          equivalencePathRefl Y) := by
  rw [replacementPathHomotopy_lift, replacementPathHomotopy_zero]
  calc
    _ = f ≫ equivalencePathRefl Y := pullback.lift_fst _ _ _
    _ = _ := by
      rw [← Category.assoc, ← Category.assoc, equivalencePathReplacementSection_projection,
        Category.id_comp]

end SerrePositivity.InfinityCategories.F2
