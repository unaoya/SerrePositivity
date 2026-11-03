module
public import SerrePositivity.InfinityCategories.DGNerve.ClosedComposition
public import SerrePositivity.InfinityCategories.DGNerve.FunctorMapping
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence

/-! # 閉次数零射による斉次前合成の微分・合成・関手性

概要：斉次元の閉射による前合成を、実微分と指定された閉射の合成に沿って計算する。
方針：Leibniz 則の零微分項と、閉射の cycle の合成公式を使う。
規約：整数次数を変更しない。使われ方：指定された商の原始元の相対持ち上げ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.HomotopyComparison
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 閉次数零射による斉次元の前合成。 -/
def dgGradedPrecompose {q x y : D} (k : ℤ) (a : GradedHom A x y k)
    (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x) :
    GradedHom A q y k :=
  compose A (D := D) (x := q) (y := x) (z := y)
    a (closedHomEquiv A D _ _ s).val (zero_add k)

/-- 前合成は次数 +1 の実微分と可換。 -/
lemma dgGradedPrecompose_d {q x y : D} (k n : ℤ) (hkn : k + 1 = n)
    (a : GradedHom A x y k)
    (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x) :
    (homObject A D q y).d k n (dgGradedPrecompose A D k a s) =
      dgGradedPrecompose A D n ((homObject A D x y).d k n a) s := by
  subst n
  let z : GradedHom A q x 0 := (closedHomEquiv A D _ _ s).val
  have hz : differential A z = 0 := (closedHomEquiv A D _ _ s).property
  change differential A (compose A (D := D) (x := q) (y := x) (z := y)
    a z (zero_add k)) = _
  rw [differential_compose, hz, compose_zero, smul_zero, add_zero]
  rfl

/-- 前合成は指定された二閉射の実合成と厳密に両立する。 -/
lemma dgGradedPrecompose_comp {p q x y : D} (k : ℤ) (a : GradedHom A x y k)
    (r : ForgetEnrichment.of (Complex A) p ⟶ ForgetEnrichment.of (Complex A) q)
    (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x) :
    dgGradedPrecompose A D k (dgGradedPrecompose A D k a s) r =
      dgGradedPrecompose A D k a (r ≫ s) := by
  unfold dgGradedPrecompose
  rw [closedHom_comp]
  exact (compose_assoc_of_sum (closedHomEquiv A D _ _ r).val
    (closedHomEquiv A D _ _ s).val a (by decide) (zero_add k) (zero_add k)).symm

/-- 前合成は斉次元の差を保つ。 -/
lemma dgGradedPrecompose_sub {q x y : D} (k : ℤ) (a b : GradedHom A x y k)
    (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x) :
    dgGradedPrecompose A D k (a - b) s =
      dgGradedPrecompose A D k a s - dgGradedPrecompose A D k b s :=
  compose_sub_left _ _ _ _

/-- 閉射による前合成は零元を保つ。 -/
lemma dgGradedPrecompose_zero {q x y : D} (k : ℤ)
    (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x) :
    dgGradedPrecompose A D k (0 : GradedHom A x y k) s = 0 :=
  zero_compose _ _

/-- 閉射による前合成は斉次閉元を保つ。 -/
lemma dgGradedPrecompose_closed {q x y : D} (k : ℤ) (a : GradedHom A x y k)
    (ha : differential A a = 0)
    (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x) :
    differential A (dgGradedPrecompose A D k a s) = 0 := by
  have h := dgGradedPrecompose_d A D k (k + 1) rfl a s
  change differential A (dgGradedPrecompose A D k a s) =
    dgGradedPrecompose A D (k + 1) (differential A a) s at h
  rw [h, ha, dgGradedPrecompose_zero]

variable (E : Type w) [DGCategory A E] (F : DGFunctor A D E)

/-- 任意の dg 関手は閉射による斉次前合成を厳密に保つ。 -/
lemma dgFunctorGradedPrecompose_map {q x y : D} (k : ℤ) (a : GradedHom A x y k)
    (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x) :
    (F.map q y).f k (dgGradedPrecompose A D k a s) =
      dgGradedPrecompose A E (q := F.obj q) (x := F.obj x) (y := F.obj y)
        k ((F.map x y).f k a) (F.onClosed.map s) := by
  unfold dgGradedPrecompose
  have hs := congrArg Subtype.val (F.closedHomEquiv_map s)
  change (closedHomEquiv A E _ _ (F.onClosed.map s)).val =
    (F.map q x).f 0 (closedHomEquiv A D _ _ s).val at hs
  have hm := map_compose F (x := q) (y := x) (z := y)
    a (closedHomEquiv A D _ _ s).val (zero_add k)
  exact hm.trans (congrArg (fun v : GradedHom A (F.obj q) (F.obj x) 0 =>
    compose A ((F.map x y).f k a) v (zero_add k)) hs.symm)

/-- 像の閉射による前合成の cycle は元の閉射の cycle の像で計算できる。 -/
lemma dgGradedPrecompose_image {q x y : D} (k : ℤ)
    (c : GradedHom A (F.obj x) (F.obj y) k)
    (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x) :
    dgGradedPrecompose A E (q := F.obj q) (x := F.obj x) (y := F.obj y)
      k c (F.onClosed.map s) =
      compose A (D := E) (x := F.obj q) (y := F.obj x) (z := F.obj y)
        c ((F.map q x).f 0 (closedHomEquiv A D _ _ s).val) (zero_add k) := by
  exact congrArg (fun v : GradedHom A (F.obj q) (F.obj x) 0 =>
    compose A (D := E) (x := F.obj q) (y := F.obj x) (z := F.obj y) c v (zero_add k))
      (congrArg Subtype.val (F.closedHomEquiv_map s))

end SerrePositivity.InfinityCategories
