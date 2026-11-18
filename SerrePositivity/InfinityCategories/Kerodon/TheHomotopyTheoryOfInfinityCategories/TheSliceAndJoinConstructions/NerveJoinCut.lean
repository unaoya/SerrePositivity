module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.NerveJoinBoundaries

/-!
概要：通常圏の join の射列の切断を、既存の始対象を補った模型から読み戻す。
方針：左側を補った始対象へ潰し、既存の initialNerveCut を適用する。
規約：切断の復元だけを扱い、左右の射列の復元と混同しない。
使われ方：HTT 1.2.8、Kerodon §4.3.2（Tag 0160）、S8 の模型比較の逆関係。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
variable {C D : Type u} [SmallCategory C] [SmallCategory D]

/-- 左因子を始対象へ潰し、右因子を指定包含で写す。
HTT 1.2.8、Kerodon §4.3.2（Tag 0160）、既存の join の関手の特殊化。 -/
def nerveJoinCollapseLeft (C D : Type u) [SmallCategory C] [SmallCategory D] :
    CategoryTheory.Join C D ⥤ WithInitial D :=
  CategoryTheory.Join.mkFunctor ((Functor.const C).obj WithInitial.star) WithInitial.incl
    { app p := WithInitial.starInitial.to (WithInitial.of p.2)
      naturality := by intro a b f; exact WithInitial.starInitial.hom_ext _ _ }

/-- 左側は補った始対象に写る。
HTT 1.2.8、Kerodon §4.3.2（Tag 0160）、潰す関手の対象の法則。 -/
lemma nerveJoinCollapseLeft_left (c : C) :
    (nerveJoinCollapseLeft C D).obj (CategoryTheory.Join.left c) = WithInitial.star := rfl

/-- 右側は元の対象に写る。
HTT 1.2.8、Kerodon §4.3.2（Tag 0160）、潰す関手の対象の法則。 -/
lemma nerveJoinCollapseLeft_right (d : D) :
    (nerveJoinCollapseLeft C D).obj (CategoryTheory.Join.right d) = WithInitial.of d := rfl

/-- 通常圏の join の射列の切断を既存の始対象の切断で読む。
HTT 1.2.8、Kerodon §4.3.2（Tag 0160）、模型比較の切断の読み戻し。 -/
def nerveJoinCut {n : ℕ} (s : ComposableArrows (CategoryTheory.Join C D) n) : ℕ :=
  initialNerveCut (s ⋙ nerveJoinCollapseLeft C D)

/-- 読み戻した切断は全頂点数以下である。
HTT 1.2.8、Kerodon §4.3.2（Tag 0160）、既存の切断の上界の特殊化。 -/
lemma nerveJoinCut_le {n : ℕ} (s : ComposableArrows (CategoryTheory.Join C D) n) :
    nerveJoinCut s ≤ n + 1 := initialNerveCut_le _

/-- 同じ join 射列から切断を読み戻すと、元の切断に厳密に戻る。
HTT 1.2.8、Kerodon §4.3.2（Tag 0160）、模型比較の逆関係の切断の部分。 -/
lemma nerveJoinCut_chain {n : ℕ} (s : Join.Simplex (nerve C) (nerve D) n) :
    nerveJoinCut (nerveJoinChain s) = s.1.val := by
  apply Join.cut_ext (nerveJoinCut_le _) (by have := s.1.isLt; omega)
  intro i
  change i.val < initialNerveCut (nerveJoinChain s ⋙ nerveJoinCollapseLeft C D) ↔ _
  rw [initialNerve_lt_cut_iff]
  change (nerveJoinCollapseLeft C D).obj (nerveJoinObj s i) = WithInitial.star ↔ _
  by_cases hi : i.val < s.1.val
  · rw [nerveJoinObj_left s i hi, nerveJoinCollapseLeft_left]
    simp [hi]
  · rw [nerveJoinObj_right s i hi, nerveJoinCollapseLeft_right]
    simp [hi]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
