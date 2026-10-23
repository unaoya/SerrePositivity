module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.AnodyneRelativeHomotopy

/-!
概要：Kan 対象の連続 Kan 置換の単位に、元の対象を固定する強変形 retract を作る。
方針：anodyne な単位を終対象への Kan fibration に対して持ち上げ、相対円柱を作る。
規約：単位の左逆は厳密、右逆の比較は単位の像上で全時刻定値。
使われ方：指定 path とその比較円柱を元の Kan 値へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open HomotopicalAlgebra SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：Kan 対象の単位は、その像を固定した強変形 retract を持つ。
方針：厳密な左逆の持ち上げと両端評価への相対持ち上げを順に取る。
規約：比較円柱は単位の像上で定値。使われ方：境界固定の Kan 置換の反映。 -/
lemma continuousKanReplacementUnit_strong_retraction (X : SSet.{u}) [KanComplex X] :
    ∃ r : continuousKanReplacement.obj X ⟶ X,
      continuousKanReplacementUnit.app X ≫ r = 𝟙 X ∧
      ∃ H : SSet.Homotopy (r ≫ continuousKanReplacementUnit.app X)
        (𝟙 (continuousKanReplacement.obj X)),
        (continuousKanReplacementUnit.app X ▷ (Δ[1] : SSet.{u})) ≫ H.h =
          fst X (Δ[1] : SSet.{u}) ≫ continuousKanReplacementUnit.app X := by
  let η : X ⟶ continuousKanReplacement.obj X := continuousKanReplacementUnit.app X
  have hi := continuousKanReplacementUnit_anodyne X
  have := hi (terminal.from X)
    (by rw [← HomotopicalAlgebra.fibration_iff]; infer_instance)
  have sq : CommSq (𝟙 X) η (terminal.from X)
      (terminal.from (continuousKanReplacement.obj X)) :=
    ⟨terminalIsTerminal.hom_ext _ _⟩
  let r := sq.lift
  have hr : η ≫ r = 𝟙 X := sq.fac_left
  have he : η ≫ (r ≫ η) = η ≫ 𝟙 _ := by
    rw [← Category.assoc, hr, Category.id_comp, Category.comp_id]
  obtain ⟨H, hH⟩ := anodyne_relative_homotopy η hi (r ≫ η) (𝟙 _) he
  refine ⟨r, hr, H, ?_⟩
  simpa only [← Category.assoc η r η, hr, Category.id_comp, Category.assoc] using hH

end SerrePositivity.InfinityCategories.F2
