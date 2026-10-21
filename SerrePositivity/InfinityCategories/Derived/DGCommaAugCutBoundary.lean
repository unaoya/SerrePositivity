module
public import SerrePositivity.InfinityCategories.Derived.DGCommaAugSimplexHomotopy
public import SerrePositivity.InfinityCategories.Derived.DGCommaAugCutDifferential
public import SerrePositivity.InfinityCategories.Derived.DGCommaAugHomotopyNaturality
/-!
概要：同じ実切断補正の微分の中間次数を正規化し、左右に元の HA 方程式を代入する。
方針：生の次数を指定する Leibniz 則と実 Hom 射影の chain map の可換性を使う。
規約：比較 cochain・元の単体・切断係数を選び直さない。
使われ方：全候補の HA 方程式に残る削除・二重切断和の相殺。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
/-- 全微分次数を指定した、同じ通常順合成の Leibniz 則。 -/
lemma dgCommaDifferential_compose_of_indices (R : Type u) [CommRing R]
    {D : Type v} [DGCategory R D] {X Y Z : D} (p q n p' q' n' : ℤ)
    (hpq : p + q = n) (hp : p + 1 = p') (hq : q + 1 = q') (hn : n + 1 = n')
    (g : GradedHom R Y Z q) (f : GradedHom R X Y p) :
    (homObject R D X Z).d n n' (compose R g f hpq) =
    compose R (n := n') ((homObject R D Y Z).d q q' g) f (by omega) +
      q.negOnePow • compose R (n := n') g ((homObject R D X Y).d p p' f) (by omega) := by
  subst p'
  subst q'
  subst n'
  exact differential_compose R g f hpq
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
/-- 指定出力次数で、同じ比較成分の微分を元の微分と比較差で解く。 -/
lemma dgCommaAugmentationHomotopyAt_differential_eq
    (X Y : DGFunctorCommaObject R C E F) (p q : ℤ) (h : p - 1 = q)
    (a : GradedHom R X Y p) :
    (homObject R E X.replacement (F.obj Y.source)).d q p
        (dgCommaAugmentationHomotopyAt R C E F X Y p q h a) =
      -(dgCommaAugmentationHomotopyAt R C E F X Y (p + 1) p (by omega)
        ((homObject R _ X Y).d p (p + 1) a) +
        (dgFunctorCommaBoundary R C E F X Y).f p a) := by
  apply eq_neg_of_add_eq_zero_left
  simpa only [add_assoc] using
    dgCommaAugmentationHomotopyAt_differential R C E F X Y p q h a
variable {n : ℕ} (s : SimplexData R (DGFunctorCommaObject R C E F) n)
/-- 右比較成分の出力次数を正規化し、左微分を同じ入力 Hom 射影へ戻す。 -/
lemma dgCommaAugmentationHomotopyCut_differential_normalized
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (j : Fin (n + 1))
    (hsum : (2 - ((I.filter (· ≤ j)).card : ℤ)) +
      (2 - ((I.filter (j ≤ ·)).card : ℤ) - 1) = k) :
    let p := 2 - ((I.filter (· ≤ j)).card : ℤ)
    let q := 2 - ((I.filter (j ≤ ·)).card : ℤ)
    let l := s.homOrZero (I.filter (· ≤ j)) a j p
    let r := s.homOrZero (I.filter (j ≤ ·)) j b q
    (homObject R E (s.obj a).replacement (F.obj (s.obj b).source)).d k (k + 1)
      (dgCommaAugmentationHomotopyCut R C E F s I a b k j) =
    compose R (x := (s.obj a).replacement) (y := (s.obj j).replacement)
      (z := F.obj (s.obj b).source) (n := k + 1)
      ((homObject R E (s.obj j).replacement (F.obj (s.obj b).source)).d (q - 1) q
        (dgCommaAugmentationHomotopyComponent R C E F (s.obj j) (s.obj b) q r))
      (((dgCommaAugmentationSource R C E F).map (s.obj a) (s.obj j)).f p l)
      (by dsimp [p, q] at *; omega) +
    (q - 1).negOnePow • compose R
      (x := (s.obj a).replacement) (y := (s.obj j).replacement)
      (z := F.obj (s.obj b).source) (n := k + 1)
      (dgCommaAugmentationHomotopyComponent R C E F (s.obj j) (s.obj b) q r)
      (((dgCommaAugmentationSource R C E F).map (s.obj a) (s.obj j)).f (p + 1)
        ((homObject R _ (s.obj a) (s.obj j)).d p (p + 1) l))
      (by dsimp [p, q] at *; omega) := by
  dsimp only
  rw [dgCommaAugmentationHomotopyCut, dite_eq_left hsum]
  have hd := dgCommaDifferential_compose_of_indices R _ _ k
    (2 - ((I.filter (· ≤ j)).card : ℤ) + 1) (2 - ((I.filter (j ≤ ·)).card : ℤ))
    (k + 1) hsum rfl
    (by omega) rfl
    (dgCommaAugmentationHomotopyComponent R C E F (s.obj j) (s.obj b) _
      (s.homOrZero (I.filter (j ≤ ·)) j b _))
    (((dgCommaAugmentationSource R C E F).map (s.obj a) (s.obj j)).f _
      (s.homOrZero (I.filter (· ≤ j)) a j _))
  have hl := ConcreteCategory.congr_hom
    (((dgCommaAugmentationSource R C E F).map (s.obj a) (s.obj j)).comm
      (2 - ((I.filter (· ≤ j)).card : ℤ)) (2 - ((I.filter (· ≤ j)).card : ℤ) + 1))
    (s.homOrZero (I.filter (· ≤ j)) a j _)
  change (homObject R E
      ((dgCommaAugmentationSource R C E F).obj (s.obj a))
      ((dgCommaAugmentationSource R C E F).obj (s.obj j))).d
      (2 - ((I.filter (· ≤ j)).card : ℤ)) (2 - ((I.filter (· ≤ j)).card : ℤ) + 1)
      (((dgCommaAugmentationSource R C E F).map (s.obj a) (s.obj j)).f _
        (s.homOrZero (I.filter (· ≤ j)) a j _)) = _ at hl
  erw [hl] at hd
  exact hd
/-- 同じ実切断の微分を、元の左右微分と実比較差へ展開する。 -/
lemma dgCommaAugmentationHomotopyCut_differential_boundary
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (j : Fin (n + 1))
    (hsum : (2 - ((I.filter (· ≤ j)).card : ℤ)) +
      (2 - ((I.filter (j ≤ ·)).card : ℤ) - 1) = k) :
    let p := 2 - ((I.filter (· ≤ j)).card : ℤ)
    let q := 2 - ((I.filter (j ≤ ·)).card : ℤ)
    let l := s.homOrZero (I.filter (· ≤ j)) a j p
    let r := s.homOrZero (I.filter (j ≤ ·)) j b q
    (homObject R E (s.obj a).replacement (F.obj (s.obj b).source)).d k (k + 1)
      (dgCommaAugmentationHomotopyCut R C E F s I a b k j) =
    compose R (x := (s.obj a).replacement) (y := (s.obj j).replacement)
      (z := F.obj (s.obj b).source) (n := k + 1)
      (-(dgCommaAugmentationHomotopyAt R C E F (s.obj j) (s.obj b) (q + 1) q (by omega)
          ((homObject R _ (s.obj j) (s.obj b)).d q (q + 1) r) +
        (dgFunctorCommaBoundary R C E F (s.obj j) (s.obj b)).f q r))
      (((dgCommaAugmentationSource R C E F).map (s.obj a) (s.obj j)).f p l)
      (by dsimp [p, q] at *; omega) +
    (q - 1).negOnePow • compose R
      (x := (s.obj a).replacement) (y := (s.obj j).replacement)
      (z := F.obj (s.obj b).source) (n := k + 1)
      (dgCommaAugmentationHomotopyComponent R C E F (s.obj j) (s.obj b) q r)
      (((dgCommaAugmentationSource R C E F).map (s.obj a) (s.obj j)).f (p + 1)
        ((homObject R _ (s.obj a) (s.obj j)).d p (p + 1) l))
      (by dsimp [p, q] at *; omega) := by
  dsimp only
  rw [dgCommaAugmentationHomotopyCut_differential_normalized R C E F s I a b k j hsum]
  have he := dgCommaAugmentationHomotopyAt_differential_eq R C E F
    (s.obj j) (s.obj b) (2 - ((I.filter (j ≤ ·)).card : ℤ)) _ rfl
    (s.homOrZero (I.filter (j ≤ ·)) j b _)
  change (homObject R E (s.obj j).replacement (F.obj (s.obj b).source)).d _ _
    (dgCommaAugmentationHomotopyComponent R C E F (s.obj j) (s.obj b) _
      (s.homOrZero (I.filter (j ≤ ·)) j b _)) = _ at he
  rw [he]
/-- 正しい元の実係数の微分は、全域表示でも同じ線形・二次境界の差。 -/
lemma dgCommaAugmentationSource_homOrZero_differential
    (s : Simplex R (DGFunctorCommaObject R C E F) n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    (homObject R _ (s.obj a) (s.obj b)).d k (k + 1)
      (s.toSimplexData.homOrZero I a b k) =
      s.toSimplexData.linearBoundary I a b k - s.toSimplexData.quadraticBoundary I a b k := by
  rw [SimplexData.homOrZero_eq s.toSimplexData I a b k hI ha hb hk]
  exact (s.equation I a b k hI ha hb hk).trans
    (SimplexData.rhs_eq_linear_sub_quadratic s.toSimplexData I a b k hI ha hb hk)
/-- 内部の同じ実切断の左右に、元の実単体の HA 方程式を代入する。 -/
lemma dgCommaAugmentationHomotopyCut_simplex_boundary
    (s : Simplex R (DGFunctorCommaObject R C E F) n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (j : Fin (n + 1))
    (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hj : j ∈ I) (haj : a < j) (hjb : j < b) :
    let p := 2 - ((I.filter (· ≤ j)).card : ℤ)
    let q := 2 - ((I.filter (j ≤ ·)).card : ℤ)
    let l := s.toSimplexData.homOrZero (I.filter (· ≤ j)) a j p
    let r := s.toSimplexData.homOrZero (I.filter (j ≤ ·)) j b q
    (homObject R E (s.obj a).replacement (F.obj (s.obj b).source)).d k (k + 1)
      (dgCommaAugmentationHomotopyCut R C E F s.toSimplexData I a b k j) =
    compose R (x := (s.obj a).replacement) (y := (s.obj j).replacement)
      (z := F.obj (s.obj b).source) (n := k + 1)
      (-(dgCommaAugmentationHomotopyAt R C E F (s.obj j) (s.obj b) (q + 1) q (by omega)
          (s.toSimplexData.linearBoundary (I.filter (j ≤ ·)) j b q -
            s.toSimplexData.quadraticBoundary (I.filter (j ≤ ·)) j b q) +
        (dgFunctorCommaBoundary R C E F (s.obj j) (s.obj b)).f q r))
      (((dgCommaAugmentationSource R C E F).map (s.obj a) (s.obj j)).f p l)
      (by dsimp [p, q]; have := Index.split_card hj; omega) +
    (q - 1).negOnePow • compose R
      (x := (s.obj a).replacement) (y := (s.obj j).replacement)
      (z := F.obj (s.obj b).source) (n := k + 1)
      (dgCommaAugmentationHomotopyComponent R C E F (s.obj j) (s.obj b) q r)
      (((dgCommaAugmentationSource R C E F).map (s.obj a) (s.obj j)).f (p + 1)
        (s.toSimplexData.linearBoundary (I.filter (· ≤ j)) a j p -
          s.toSimplexData.quadraticBoundary (I.filter (· ≤ j)) a j p))
      (by dsimp [p, q]; have := Index.split_card hj; omega) := by
  dsimp only
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
  have hl := dgCommaAugmentationSource_homOrZero_differential R C E F s
    (I.filter (· ≤ j)) a j _ hL (Index.left_min hamin haj.le _) (Index.left_max hj _) rfl
  have hr := dgCommaAugmentationSource_homOrZero_differential R C E F s
    (I.filter (j ≤ ·)) j b _ hR (Index.right_min hj _) (Index.right_max hbmax hjb.le _) rfl
  have he := dgCommaAugmentationHomotopyCut_differential_boundary R C E F
    s.toSimplexData I a b k j hsum
  dsimp only at he
  rw [hl, hr] at he
  exact he
end SerrePositivity.InfinityCategories
