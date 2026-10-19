module
public import SerrePositivity.InfinityCategories.Derived.DGSourceRefinementComposition

/-! # 任意次数の単体データの閉始点細分と rhs の輸送

概要：全斉次成分を順方向 Hom の線形写像で写し、全ての rhs が同じ写像で移ることを示す。
方針：内部頂点ごとの符号・差・合成の保存から有限和の保存へ進む。
規約：微分方程式は入力に課さない。使われ方：実高次単体の始点細分。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
variable {n : ℕ} (t : SimplexData A D n) (q : D)
variable (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) (t.obj 0))

/-- 全斉次成分を同じ閉始点細分で写した、任意次数の実データ。 -/
def dgSimplexDataInitialRefinement : SimplexData A D n where
  obj := dgSourceRefinementObj D t.obj q
  hom I a b k hI ha hb hk :=
    dgSourceRefinementHomLinear A D t.obj q s a b k (t.hom I a b k hI ha hb hk)

/-- 各内部頂点の rhs 寄与は、同じ順方向 Hom の線形写像で移る。 -/
lemma dgSimplexDataInitialRefinement_term
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (j : Fin (n + 1)) (hj : j ∈ I) (haj : a < j) (hjb : j < b) :
    dgSourceRefinementHomLinear A D t.obj q s a b (k + 1)
      (t.term I a b k hI ha hb hk j hj haj hjb) =
      (dgSimplexDataInitialRefinement A D t q s).term I a b k hI ha hb hk j hj haj hjb := by
  simp only [SimplexData.term, dgSimplexDataInitialRefinement, Units.smul_def, map_zsmul,
    map_sub, dgSourceRefinementHomLinear_compose A D t.obj q s a j b haj hjb]

/-- 全ての rhs は、始点細分に伴う同じ順方向 Hom の線形写像で移る。 -/
lemma dgSimplexDataInitialRefinement_rhs
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    dgSourceRefinementHomLinear A D t.obj q s a b (k + 1) (t.rhs I a b k hI ha hb hk) =
      (dgSimplexDataInitialRefinement A D t q s).rhs I a b k hI ha hb hk := by
  unfold SimplexData.rhs
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hint : a < j.val ∧ j.val < b
  · simp only [dite_eq_left hint, dgSimplexDataInitialRefinement_term]
  · simp only [dite_eq_right hint, map_zero]

end SerrePositivity.InfinityCategories
