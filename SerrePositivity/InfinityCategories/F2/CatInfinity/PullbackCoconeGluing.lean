module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeCoconeAbsolute
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
概要：像の全余錐が一致する二成分の余錐を引き戻し内へ貼る。
方針：全余錐の射を通常の引き戻しへ合わせ、図式の固定条件を両射影で照合する。
規約：元の図式と選んだ両成分の全余錐を厳密に保持する。
使われ方：lax pullback の余極限錐の存在構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：適合した二成分の余錐を元の引き戻し図式の余錐へ合わせる。
方針：元の二つの全余錐の射に引き戻しの lift を適用する。
規約：この貼り合わせは充填性も余極限性も要求しない。
使われ方：両入力の全余錐を保つ余極限の存在。 -/
lemma exists_cocone_pullback_with_components {J E D B : SSet.{u}}
    (p : E ⟶ B) (q : D ⟶ B) (r : J ⟶ pullback p q)
    (ce : JoinCocone (r ≫ pullback.fst p q)) (cd : JoinCocone (r ≫ pullback.snd p q))
    (h : ce.val ≫ p = cd.val ≫ q) :
    ∃ c : JoinCocone r, F1B.kanPostcomposeCocone (pullback.fst p q) c = ce ∧
      F1B.kanPostcomposeCocone (pullback.snd p q) c = cd := by
  let c : JoinCocone r := ⟨pullback.lift ce.val cd.val h, by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst]
      exact ce.property
    · rw [Category.assoc, pullback.lift_snd]
      exact cd.property⟩
  refine ⟨c, ?_, ?_⟩
  · apply Subtype.ext
    exact pullback.lift_fst _ _ _
  · apply Subtype.ext
    exact pullback.lift_snd _ _ _

end SerrePositivity.InfinityCategories.F2
