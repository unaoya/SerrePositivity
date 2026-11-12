module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalEndpointPullback

/-!
概要：直積の二つの因子の射の自然性の正方形の pullback 性。
方針：各射影の成分から一意な持ち上げを作る。
規約：どちらの射にも単射性を要求しない。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の fat join の右因子の比較。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：二つの因子で独立に作用する直積の自然性の正方形は pullback。
方針：左側の射から第一成分、上側の射から第二成分を取る。
規約：二つの射は任意。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の円柱の両端の逆像。 -/
lemma isPullback_whisker_exchange {A B C D : SSet.{u}} (i : A ⟶ B) (j : C ⟶ D) :
    IsPullback (i ▷ C) (A ◁ j) (B ◁ j) (i ▷ D) := by
  apply IsPullback.mk' (whisker_exchange i j).symm
  · intro T φ ψ h₁ h₂
    apply CartesianMonoidalCategory.hom_ext
    · simpa using h₂ =≫ fst A D
    · simpa using h₁ =≫ snd B C
  · intro T a b h
    refine ⟨lift (b ≫ fst A D) (a ≫ snd B C), ?_, ?_⟩
    · apply CartesianMonoidalCategory.hom_ext
      · simpa using (h =≫ fst B D).symm
      · simp
    · apply CartesianMonoidalCategory.hom_ext
      · simp
      · simpa using h =≫ snd B D

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
