module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.NerveJoinPostcomposition

/-!
概要：nerve と join の比較の左右の制限は、元の圏の指定包含である。
方針：切断が全頂点数または零の射列を全対象・全射で照合する。
規約：端点での一致だけでなく、包含後の全単体的射を比較する。
使われ方：HTT 1.2.8、Kerodon §4.3.2（Tag 0160）、S8 の両端射影の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
variable {C D : Type u} [SmallCategory C] [SmallCategory D]

/-- 左だけの射列の対象は指定した左包含である。
HTT 1.2.8、Kerodon §4.3.2（Tag 0160）、比較射の制限の法則。 -/
lemma nerveJoinObj_inl {n : ℕ} (s : ComposableArrows C n) (i : Fin (n + 1)) :
    nerveJoinObj (Join.Simplex.inl (K := nerve C) (L := nerve D) s) i = CategoryTheory.Join.left (s.obj i) := by
  rw [nerveJoinObj_left _ i i.isLt]
  rfl

/-- 右だけの射列の対象は指定した右包含である。
HTT 1.2.8、Kerodon §4.3.2（Tag 0160）、比較射の制限の法則。 -/
lemma nerveJoinObj_inr {n : ℕ} (s : ComposableArrows D n) (i : Fin (n + 1)) :
    nerveJoinObj (Join.Simplex.inr (K := nerve C) (L := nerve D) s) i = CategoryTheory.Join.right (s.obj i) := by
  rw [nerveJoinObj_right _ i (Nat.not_lt_zero _)]
  rfl

/-- 左だけの全射列は元の射列と左包含の合成である。
HTT 1.2.8、Kerodon §4.3.2（Tag 0160）、比較射の制限の法則。 -/
lemma nerveJoinChain_inl {n : ℕ} (s : ComposableArrows C n) :
    nerveJoinChain (Join.Simplex.inl (K := nerve C) (L := nerve D) s) = s ⋙ CategoryTheory.Join.inclLeft C D := by
  refine CategoryTheory.Functor.hext (nerveJoinObj_inl s) ?_
  intro i j h
  change HEq (nerveJoinMap (Join.Simplex.inl (K := nerve C) (L := nerve D) s) (leOfHom h)) _
  have hi : i.val < (Join.Simplex.inl (K := nerve C) (L := nerve D) s).1.val := i.isLt
  have hj : j.val < (Join.Simplex.inl (K := nerve C) (L := nerve D) s).1.val := j.isLt
  simp only [nerveJoinMap, dite_eq_left hi, dite_eq_left hj,
    eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  rfl

/-- 右だけの全射列は元の射列と右包含の合成である。
HTT 1.2.8、Kerodon §4.3.2（Tag 0160）、比較射の制限の法則。 -/
lemma nerveJoinChain_inr {n : ℕ} (s : ComposableArrows D n) :
    nerveJoinChain (Join.Simplex.inr (K := nerve C) (L := nerve D) s) = s ⋙ CategoryTheory.Join.inclRight C D := by
  refine CategoryTheory.Functor.hext (nerveJoinObj_inr s) ?_
  intro i j h
  change HEq (nerveJoinMap (Join.Simplex.inr (K := nerve C) (L := nerve D) s) (leOfHom h)) _
  have hi : ¬ i.val < (Join.Simplex.inr (K := nerve C) (L := nerve D) s).1.val := Nat.not_lt_zero _
  simp only [nerveJoinMap, dite_eq_right hi,
    eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  rfl

/-- 左因子への制限は、元の通常圏の指定包含の nerve と厳密に一致する。
HTT 1.2.8、Kerodon §4.3.2（Tag 0160）、全単体的比較の制限の法則。 -/
lemma joinInl_nerveJoinComparison :
    joinInl (nerve C) (nerve D) ≫ nerveJoinComparison C D =
      nerveMap (CategoryTheory.Join.inclLeft C D) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  exact nerveJoinChain_inl s

/-- 右因子への制限は、元の通常圏の指定包含の nerve と厳密に一致する。
HTT 1.2.8、Kerodon §4.3.2（Tag 0160）、全単体的比較の制限の法則。 -/
lemma joinInr_nerveJoinComparison :
    joinInr (nerve C) (nerve D) ≫ nerveJoinComparison C D =
      nerveMap (CategoryTheory.Join.inclRight C D) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  exact nerveJoinChain_inr s

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
