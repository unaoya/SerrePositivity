module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedSum

/-! # 右 pinched 線形化で最小点の項を復元する有限和

概要：二番目の点だけに現れる補正項を最小点の削除項に直す。
方針：最小点と二番目の点の係数が逆符号であることと有限和の加法性を使う。
規約：Kerodon §4.6.5（Tag 01KW）、N0.3 の cochain 符号。使われ方：全線形右辺との同定。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section

namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：最小点以外の線形化した寄与の和は全ての削除項の和。
方針：二番目の点の補正項を取り出し、逆符号の係数で最小点の項に戻す。
規約：Kerodon §4.6.5（Tag 01KW）、N0.3 の cochain 符号。使われ方：線形方程式の右辺の復元。 -/
lemma sum_linear_terms {n : ℕ} {M : Type*} [AddCommGroup M]
    (J : Finset (Fin (n + 1))) (hJ : 2 ≤ J.card) (f : J → M) :
    (∑ j : J, if J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ) < j.val then
      (((J.filter (j.val < ·)).card : ℤ) + 1).negOnePow •
        (f j - if j.val = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.second J hJ then f ⟨J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ), J.min'_mem _⟩ else 0)
      else 0) = ∑ j : J, (((J.filter (j.val < ·)).card : ℤ) + 1).negOnePow • f j := by
  let a : J := ⟨J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ), J.min'_mem _⟩
  let b : J := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.second J hJ, (Finset.mem_erase.mp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.second_mem_erase J hJ)).2⟩
  let c (j : J) : ℤˣ := (((J.filter (j.val < ·)).card : ℤ) + 1).negOnePow
  have hab : a ≠ b := by
    intro he
    exact (ne_of_lt (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.first_lt_second J hJ)) (congrArg Subtype.val he)
  have hval : c b = -c a := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.sign_second J hJ
  change (∑ j : J, if a.val < j.val then c j • (f j - if j.val = b.val then f a else 0) else 0) =
    ∑ j : J, c j • f j
  have hpoint : ∀ j : J,
      (if a.val < j.val then c j • (f j - if j.val = b.val then f a else 0) else 0) =
        (if j = a then 0 else c j • f j) - (if j = b then c b • f a else 0) := by
    intro j
    by_cases hja : j = a
    · subst j
      simp [hab]
    · have haj : a.val < j.val := lt_of_le_of_ne
        (show a.val ≤ j.val from (J.isLeast_min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)).2 j.property)
        (fun he => hja (Subtype.ext he.symm))
      by_cases hjb : j = b
      · subst j
        simp [haj, hja, smul_sub]
      · have hne : j.val ≠ b.val := fun he => hjb (Subtype.ext he)
        simp [haj, hja, hjb, hne]
  have hsum : (∑ j : J, if j = a then 0 else c j • f j) + c a • f a = ∑ j : J, c j • f j := by
    calc
      _ = (∑ j : J, if j = a then 0 else c j • f j) +
          (∑ j : J, if j = a then c a • f a else 0) := by simp
      _ = ∑ j : J, ((if j = a then 0 else c j • f j) +
          (if j = a then c a • f a else 0)) := Finset.sum_add_distrib.symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases he : j = a <;> simp [he]
  calc
    _ = ∑ j : J, ((if j = a then 0 else c j • f j) -
        (if j = b then c b • f a else 0)) := by
      apply Finset.sum_congr rfl
      intro j _
      exact hpoint j
    _ = (∑ j : J, if j = a then 0 else c j • f j) - c b • f a := by
      rw [Finset.sum_sub_distrib]
      simp
    _ = (∑ j : J, if j = a then 0 else c j • f j) + c a • f a := by
      rw [hval]
      simp [Units.smul_def]
    _ = _ := hsum

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
