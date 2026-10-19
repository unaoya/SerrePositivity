module

public import SerrePositivity.InfinityCategories.F2.TensorCoconeComponentCriterion

/-!
概要：選んだ両成分の余極限余錐を厳密に保つ直積の余極限錐の存在。
方針：二つの全余錐の射を直積に合わせ、成分ごとの普遍性を使う。
規約：元の図式と選んだ二つの全余錐を保持する。
使われ方：lax pullback の入力の余極限錐。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：指定した両成分の余極限余錐を保つ直積内の余極限錐が存在する。
方針：全余錐の射の直積を作り、元の図式の固定条件を両射影で確認する。
規約：両射影との一致は全余錐の等式。
使われ方：選んだ入力を保つ lax pullback の余極限。 -/
lemma exists_colimitCone_tensor_with_components {J X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (r : J ⟶ X ⊗ Y)
    (cx : JoinCocone (r ≫ fst X Y)) (cy : JoinCocone (r ≫ snd X Y))
    (hx : IsColimitCone cx) (hy : IsColimitCone cy) :
    ∃ c : JoinCocone r, IsColimitCone c ∧ F1B.kanPostcomposeCocone (fst X Y) c = cx ∧
      F1B.kanPostcomposeCocone (snd X Y) c = cy := by
  let c : JoinCocone r := ⟨CartesianMonoidalCategory.lift cx.val cy.val, by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst]
      exact cx.property
    · rw [Category.assoc, lift_snd]
      exact cy.property⟩
  have hcx : F1B.kanPostcomposeCocone (fst X Y) c = cx := Subtype.ext (lift_fst _ _)
  have hcy : F1B.kanPostcomposeCocone (snd X Y) c = cy := Subtype.ext (lift_snd _ _)
  exact ⟨c, isColimitCone_tensor_of_components c (hcx.symm ▸ hx) (hcy.symm ▸ hy), hcx, hcy⟩

end SerrePositivity.InfinityCategories.F2
