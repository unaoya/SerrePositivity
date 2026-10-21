module
public import SerrePositivity.InfinityCategories.Derived.DGCommaAugPrismBoundary
public import SerrePositivity.InfinityCategories.DGNerve.NestedCut
/-!
概要：実 augmentation の切断補正を、既存の全域化された Hom 係数で表す。
方針：端点・濃度・次数の不一致を零とする homOrZero と、同じ次数 −1 比較成分を使う。
規約：元の正しい切断では同じ実係数へ厳密に戻る。使われ方：全 HA 方程式の二重切断和。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  {n : ℕ} (s : SimplexData R (DGFunctorCommaObject R C E F) n)
/-- 証明引数を全域化した、同じ augmentation の実切断補正。 -/
def dgCommaAugmentationHomotopyCut (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (j : Fin (n + 1)) :
    GradedHom R (s.obj a).replacement (F.obj (s.obj b).source) k :=
  if h : (2 - ((I.filter (· ≤ j)).card : ℤ)) +
      (2 - ((I.filter (j ≤ ·)).card : ℤ) - 1) = k then
    compose R (x := (s.obj a).replacement) (y := (s.obj j).replacement)
      (z := F.obj (s.obj b).source)
      (dgCommaAugmentationHomotopyComponent R C E F (s.obj j) (s.obj b) _
        (s.homOrZero (I.filter (j ≤ ·)) j b (2 - ((I.filter (j ≤ ·)).card : ℤ))))
      (((dgCommaAugmentationSource R C E F).map (s.obj a) (s.obj j)).f _
        (s.homOrZero (I.filter (· ≤ j)) a j (2 - ((I.filter (· ≤ j)).card : ℤ)))) h
  else 0
/-- 次数不一致の全域切断補正は零。 -/
lemma dgCommaAugmentationHomotopyCut_of_degree_ne (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (j : Fin (n + 1))
    (h : (2 - ((I.filter (· ≤ j)).card : ℤ)) +
      (2 - ((I.filter (j ≤ ·)).card : ℤ) - 1) ≠ k) :
    dgCommaAugmentationHomotopyCut R C E F s I a b k j = 0 := by
  rw [dgCommaAugmentationHomotopyCut, dite_eq_right h]
/-- 正しい実内部切断では、全域表示は元の同じ符号付き係数を回収する。 -/
lemma dgCommaAugmentationPrismCut_eq_homotopyCut
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (j : Fin (n + 1)) (hj : j ∈ I) (haj : a < j) (hjb : j < b) :
    dgCommaAugmentationPrismCut R C E F s I a b k hI ha hb hk j hj haj hjb =
      Index.sign I j • dgCommaAugmentationHomotopyCut R C E F s I a b k j := by
  have hamin : IsLeast (I : Set (Fin (n + 1))) a := by
    rw [ha]; exact I.isLeast_min' _
  have hbmax : IsGreatest (I : Set (Fin (n + 1))) b := by
    rw [hb]; exact I.isGreatest_max' _
  have hL := Index.left_two hamin.1 hj haj
  have hR := Index.right_two hj hbmax.1 hjb
  have hsum : (2 - ((I.filter (· ≤ j)).card : ℤ)) +
      (2 - ((I.filter (j ≤ ·)).card : ℤ) - 1) = k := by
    have := Index.split_card hj
    omega
  rw [dgCommaAugmentationHomotopyCut, dite_eq_left hsum,
    SimplexData.homOrZero_eq s _ _ _ _ hR
      (Index.right_min hj _) (Index.right_max hbmax hjb.le _) rfl,
    SimplexData.homOrZero_eq s _ _ _ _ hL
      (Index.left_min hamin haj.le _) (Index.left_max hj _) rfl]
  rfl
end SerrePositivity.InfinityCategories
