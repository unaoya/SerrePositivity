module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PullbackCoconeGluing
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ColimitConeImageStrictification
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.PullbackSquareCoconeCriterion
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoconeValEquality

/-!
概要：選んだ第二成分の余極限余錐を厳密に保つ引き戻し内の余極限余錐の存在。
方針：第一の錐の像を第二の像へ厳密化し、元の図式の錐を貼り合わせる。
規約：元の図式と第二成分の全余錐を保持する。
使われ方：lax pullback の両入力を固定した余極限余錐の構成。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：第二成分の指定余極限余錐を保つ引き戻し内の余極限余錐が存在する。
方針：二つの像の余極限余錐の同型を持ち上げ、厳密に適合する成分を貼る。
規約：第一成分も余極限余錐であり、元の図式 r を固定する。
使われ方：lax pullback の入力の余極限余錐からの存在構成。 -/
lemma exists_colimitCone_pullback_with_snd {J E D B : SSet.{u}}
    [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (p : E ⟶ B) (q : D ⟶ B) (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting p)
    (r : J ⟶ pullback p q) (ce₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (r ≫ pullback.fst p q))
    (cd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (r ≫ pullback.snd p q))
    (he₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone ce₀)
    (he₀p : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanPostcomposeCocone p ce₀))
    (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone cd) (hdq : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanPostcomposeCocone q cd)) :
    ∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone r, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanPostcomposeCocone (pullback.fst p q) c) ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanPostcomposeCocone (pullback.snd p q) c = cd := by
  have : InnerFibration p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting.innerFibration hp
  let db : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone ((r ≫ pullback.fst p q) ≫ p) := ⟨cd.val ≫ q, by
    rw [← Category.assoc, cd.property, Category.assoc, Category.assoc, pullback.condition]⟩
  have hdb : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone db :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isColimitCone_iff_of_cocone_val_eq db (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanPostcomposeCocone q cd) rfl).2 hdq
  obtain ⟨ce, he, hep⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.exists_colimitCone_with_specified_image p hp ce₀ he₀ he₀p db hdb
  have hw : ce.val ≫ p = cd.val ≫ q := congrArg Subtype.val hep
  obtain ⟨c, hc₁, hc₂⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.exists_cocone_pullback_with_components p q r ce cd hw
  have hc₁l : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanPostcomposeCocone (pullback.fst p q) c) := hc₁.symm ▸ he
  refine ⟨c, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_of_isPullback_of_components
    (IsPullback.of_hasPullback p q) c hc₁l ?_ ?_, hc₁l, hc₂⟩
  · exact hc₂.symm ▸ hd
  · rw [hc₁, hep]
    exact hdb

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
