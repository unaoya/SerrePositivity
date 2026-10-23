module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.PullbackConeGluing
public import SerrePositivity.InfinityCategories.F2.CatInfinity.LimitConeImageStrictification
public import SerrePositivity.InfinityCategories.F2.CatInfinity.PullbackConeComponentCriterion
public import SerrePositivity.InfinityCategories.F2.CatInfinity.ConeValEquality

/-!
概要：選んだ第二成分の極限錐を厳密に保つ引き戻し内の極限錐の存在。
方針：第一の錐の像を第二の像へ厳密化し、元の図式の錐を貼り合わせる。
規約：元の図式と第二成分の全錐を保持する。
使われ方：lax pullback の両入力を固定した極限錐の構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：第二成分の指定極限錐を保つ引き戻し内の極限錐が存在する。
方針：二つの像の極限錐の同型を持ち上げ、厳密に適合する成分を貼る。
規約：第一成分も極限錐であり、元の図式 r を固定する。
使われ方：lax pullback の入力の極限錐からの存在構成。 -/
lemma exists_limitCone_pullback_with_snd {J E D B : SSet.{u}}
    [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (p : E ⟶ B) (q : D ⟶ B) (hp : F1B.KanEquivalenceLifting p)
    (r : J ⟶ pullback p q) (ce₀ : JoinCone (r ≫ pullback.fst p q))
    (cd : JoinCone (r ≫ pullback.snd p q))
    (he₀ : IsLimitCone ce₀) (he₀p : IsLimitCone (mapJoinCone p ce₀))
    (hd : IsLimitCone cd) (hdq : IsLimitCone (mapJoinCone q cd)) :
    ∃ c : JoinCone r, IsLimitCone c ∧ IsLimitCone (mapJoinCone (pullback.fst p q) c) ∧
      mapJoinCone (pullback.snd p q) c = cd := by
  have : InnerFibration p := F1B.KanEquivalenceLifting.innerFibration hp
  let db : JoinCone ((r ≫ pullback.fst p q) ≫ p) := ⟨cd.val ≫ q, by
    rw [← Category.assoc, cd.property, Category.assoc, Category.assoc, pullback.condition]⟩
  have hdb : IsLimitCone db :=
    (isLimitCone_iff_of_cone_val_eq db (mapJoinCone q cd) rfl).2 hdq
  obtain ⟨ce, he, hep⟩ := exists_limitCone_with_specified_image p hp ce₀ he₀ he₀p db hdb
  have hw : ce.val ≫ p = cd.val ≫ q := congrArg Subtype.val hep
  obtain ⟨c, hc₁, hc₂⟩ := exists_cone_pullback_with_components p q r ce cd hw
  have hc₁l : IsLimitCone (mapJoinCone (pullback.fst p q) c) := hc₁.symm ▸ he
  refine ⟨c, isLimitCone_pullback_of_components p q c hc₁l ?_ ?_, hc₁l, hc₂⟩
  · exact hc₂.symm ▸ hd
  · rw [hc₁, hep]
    exact hdb

end SerrePositivity.InfinityCategories.F2
