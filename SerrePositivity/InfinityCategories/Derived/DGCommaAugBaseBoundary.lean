module
public import SerrePositivity.InfinityCategories.Derived.DGCommaAugCorrectionDifferential
/-!
概要：同じ augmentation による基底後合成を実 Hom chain map とし、元の HA を移す。
方針：実入力射影と実後合成を合成し、chain map の可換性を同じ実係数で評価する。
規約：次数や対象を選び直さない。使われ方：候補の基底微分と線形・二次境界の照合。
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
/-- 同じ実入力射影の像と augmentation の後合成からなる全 Hom chain map。 -/
def dgCommaAugmentationBaseHomMap (X Y : DGFunctorCommaObject R C E F) :
    homObject R _ X Y ⟶ homObject R E X.replacement (F.obj Y.source) :=
  (dgCommaAugmentationSource R C E F).map X Y ≫
    dgClosedPostcomposition R E (x := X.replacement) Y.augmentation
/-- 全整数次数で、同じ基底 chain map の成分は元の実合成。 -/
lemma dgCommaAugmentationBaseHomMap_apply
    (X Y : DGFunctorCommaObject R C E F) (k : ℤ) (a : GradedHom R X Y k) :
    (dgCommaAugmentationBaseHomMap R C E F X Y).f k a =
    compose R (x := X.replacement) (y := Y.replacement) (z := F.obj Y.source)
      (dgCommaAugmentationComponent R C E F Y).val
      (((dgCommaAugmentationSource R C E F).map X Y).f k a) (add_zero k) := by
  change (dgClosedPostcomposition R E (x := X.replacement) Y.augmentation).f k
    (((dgCommaAugmentationSource R C E F).map X Y).f k a) = _
  exact dgClosedPostcomposition_f R E (x := X.replacement) (y := Y.replacement)
    (z := F.obj Y.source) Y.augmentation k
    (((dgCommaAugmentationSource R C E F).map X Y).f k a)
/-- 同じ実基底係数の微分は、元の HA の線形・二次境界の像。 -/
lemma dgCommaAugmentationBase_simplex_differential {n : ℕ}
    (s : Simplex R (DGFunctorCommaObject R C E F) n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    (homObject R E (s.obj a).replacement (F.obj (s.obj b).source)).d k (k + 1)
      (compose R (x := (s.obj a).replacement) (y := (s.obj b).replacement)
        (z := F.obj (s.obj b).source) (dgCommaAugmentationComponent R C E F (s.obj b)).val
        (((dgCommaAugmentationSource R C E F).map (s.obj a) (s.obj b)).f k
          (s.hom I a b k hI ha hb hk)) (add_zero k)) =
      (dgCommaAugmentationBaseHomMap R C E F (s.obj a) (s.obj b)).f (k + 1)
        (s.toSimplexData.linearBoundary I a b k - s.toSimplexData.quadraticBoundary I a b k) := by
  rw [← dgCommaAugmentationBaseHomMap_apply]
  have he := ConcreteCategory.congr_hom
    ((dgCommaAugmentationBaseHomMap R C E F (s.obj a) (s.obj b)).comm k (k + 1))
    (s.hom I a b k hI ha hb hk)
  change (homObject R E (s.obj a).replacement (F.obj (s.obj b).source)).d k (k + 1)
    ((dgCommaAugmentationBaseHomMap R C E F (s.obj a) (s.obj b)).f k
      (s.hom I a b k hI ha hb hk)) =
    (dgCommaAugmentationBaseHomMap R C E F (s.obj a) (s.obj b)).f (k + 1)
      ((homObject R _ (s.obj a) (s.obj b)).d k (k + 1)
        (s.hom I a b k hI ha hb hk)) at he
  have hs := s.equation I a b k hI ha hb hk
  rw [SimplexData.rhs_eq_linear_sub_quadratic] at hs
  change (homObject R _ (s.obj a) (s.obj b)).d k (k + 1)
    (s.hom I a b k hI ha hb hk) = _ at hs
  rw [hs] at he
  exact he
end SerrePositivity.InfinityCategories
