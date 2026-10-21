module
public import SerrePositivity.InfinityCategories.Derived.DGCommaAugBoundaryHomotopy
/-!
概要：元の同じ実単体の HA 方程式を、augmentation の実比較成分の全微分式へ代入する。
方針：実線形・二次境界への比較 cochain の作用を、同じ削除・左右切断和へ展開する。
規約：混合候補全体の HA 方程式は別工程。使われ方：全 prism の補正和の一般微分計算。
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
  {n : ℕ} (s : Simplex R (DGFunctorCommaObject R C E F) n)
/-- 同じ実単体の線形・二次境界を代入した、全比較成分の微分式。 -/
lemma dgCommaAugmentationHomotopyAt_simplex_equation
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    (homObject R E (s.obj a).replacement (F.obj (s.obj b).source)).d (k - 1) k
        (dgCommaAugmentationHomotopyAt R C E F (s.obj a) (s.obj b) k (k - 1) rfl
          (s.hom I a b k hI ha hb hk)) +
      (dgCommaAugmentationHomotopyAt R C E F (s.obj a) (s.obj b) (k + 1) k (by omega)
          (s.toSimplexData.linearBoundary I a b k) -
        dgCommaAugmentationHomotopyAt R C E F (s.obj a) (s.obj b) (k + 1) k (by omega)
          (s.toSimplexData.quadraticBoundary I a b k)) +
      (dgFunctorCommaBoundary R C E F (s.obj a) (s.obj b)).f k
        (s.hom I a b k hI ha hb hk) = 0 := by
  have hs := s.equation I a b k hI ha hb hk
  rw [SimplexData.rhs_eq_linear_sub_quadratic] at hs
  change (homObject R _ (s.obj a) (s.obj b)).d k (k + 1)
    (s.hom I a b k hI ha hb hk) = _ at hs
  have hc : dgCommaAugmentationHomotopyAt R C E F (s.obj a) (s.obj b)
        (k + 1) k (by omega)
        ((homObject R _ (s.obj a) (s.obj b)).d k (k + 1) (s.hom I a b k hI ha hb hk)) =
      dgCommaAugmentationHomotopyAt R C E F (s.obj a) (s.obj b) (k + 1) k (by omega)
          (s.toSimplexData.linearBoundary I a b k) -
        dgCommaAugmentationHomotopyAt R C E F (s.obj a) (s.obj b) (k + 1) k (by omega)
          (s.toSimplexData.quadraticBoundary I a b k) := by
    have he := congrArg (fun x ↦ dgCommaAugmentationHomotopyAt R C E F
      (s.obj a) (s.obj b) (k + 1) k (by omega) x) hs
    simpa only [dgCommaAugmentationHomotopyAt, map_sub] using! he
  have he := dgCommaAugmentationHomotopyAt_differential R C E F
    (s.obj a) (s.obj b) k (k - 1) rfl (s.hom I a b k hI ha hb hk)
  rw [hc] at he
  exact he
/-- 同じ実単体の比較微分式を、削除係数と左右の実切断補正の全有限和へ展開する。 -/
lemma dgCommaAugmentationHomotopyAt_simplex_expansion
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    (homObject R E (s.obj a).replacement (F.obj (s.obj b).source)).d (k - 1) k
        (dgCommaAugmentationHomotopyAt R C E F (s.obj a) (s.obj b) k (k - 1) rfl
          (s.hom I a b k hI ha hb hk)) +
      ((∑ j ∈ Index.interior I a b, Index.sign I j •
          dgCommaAugmentationHomotopyAt R C E F (s.obj a) (s.obj b) (k + 1) k (by omega)
            (s.toSimplexData.homOrZero (I.erase j) a b (k + 1))) -
        ∑ j ∈ Index.interior I a b, Index.sign I j •
          ((2 - ((I.filter (j ≤ ·)).card : ℤ)).negOnePow •
            dgCommaAugmentationImageCut R C E F s.toSimplexData I a b k j +
            dgCommaAugmentationHomotopyCut R C E F s.toSimplexData I a b k j)) +
      (dgFunctorCommaBoundary R C E F (s.obj a) (s.obj b)).f k
        (s.hom I a b k hI ha hb hk) = 0 := by
  have he := dgCommaAugmentationHomotopyAt_simplex_equation R C E F s I a b k hI ha hb hk
  rw [dgCommaAugmentationHomotopyAt_linearBoundary,
    dgCommaAugmentationHomotopyAt_quadraticBoundary R C E F s.toSimplexData I a b k hk] at he
  exact he
end SerrePositivity.InfinityCategories
