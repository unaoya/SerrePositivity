module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ClosedComposition
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FunctorMapping
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 閉次数零射による斉次元の前合成。 -/
def dgGradedPrecompose {q x y : D} (k : ℤ) (a : _root_.SerrePositivity.DifferentialGraded.GradedHom A x y k)
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x) :
    _root_.SerrePositivity.DifferentialGraded.GradedHom A q y k :=
  _root_.SerrePositivity.DifferentialGraded.compose A (D := D) (x := q) (y := x) (z := y)
    a (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D _ _ s).val (zero_add k)

/-- 前合成は次数 +1 の実微分と可換。 -/
lemma dgGradedPrecompose_d {q x y : D} (k n : ℤ) (hkn : k + 1 = n)
    (a : _root_.SerrePositivity.DifferentialGraded.GradedHom A x y k)
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x) :
    (_root_.SerrePositivity.DifferentialGraded.homObject A D q y).d k n (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D k a s) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D n ((homObject A D x y).d k n a) s := by
  subst n
  let z : _root_.SerrePositivity.DifferentialGraded.GradedHom A q x 0 := (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D _ _ s).val
  have hz : _root_.SerrePositivity.DifferentialGraded.differential A z = 0 := (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D _ _ s).property
  change _root_.SerrePositivity.DifferentialGraded.differential A (compose A (D := D) (x := q) (y := x) (z := y)
    a z (zero_add k)) = _
  rw [_root_.SerrePositivity.DifferentialGraded.differential_compose, hz, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero, smul_zero, add_zero]
  rfl

/-- 前合成は指定された二閉射の実合成と厳密に両立する。 -/
lemma dgGradedPrecompose_comp {p q x y : D} (k : ℤ) (a : _root_.SerrePositivity.DifferentialGraded.GradedHom A x y k)
    (r : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) p ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q)
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D k (dgGradedPrecompose A D k a s) r =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D k a (r ≫ s) := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.closedHom_comp]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.compose_assoc_of_sum (closedHomEquiv A D _ _ r).val
    (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D _ _ s).val a (by decide) (zero_add k) (zero_add k)).symm

/-- 前合成は斉次元の差を保つ。 -/
lemma dgGradedPrecompose_sub {q x y : D} (k : ℤ) (a b : _root_.SerrePositivity.DifferentialGraded.GradedHom A x y k)
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D k (a - b) s =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D k a s - _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D k b s :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sub_left _ _ _ _

/-- 閉射による前合成は零元を保つ。 -/
lemma dgGradedPrecompose_zero {q x y : D} (k : ℤ)
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D k (0 : GradedHom A x y k) s = 0 :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose _ _

/-- 閉射による前合成は斉次閉元を保つ。 -/
lemma dgGradedPrecompose_closed {q x y : D} (k : ℤ) (a : _root_.SerrePositivity.DifferentialGraded.GradedHom A x y k)
    (ha : _root_.SerrePositivity.DifferentialGraded.differential A a = 0)
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x) :
    _root_.SerrePositivity.DifferentialGraded.differential A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D k a s) = 0 := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose_d A D k (k + 1) rfl a s
  change _root_.SerrePositivity.DifferentialGraded.differential A (dgGradedPrecompose A D k a s) =
    dgGradedPrecompose A D (k + 1) (_root_.SerrePositivity.DifferentialGraded.differential A a) s at h
  rw [h, ha, dgGradedPrecompose_zero]

variable (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory A E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E)

/-- 任意の dg 関手は閉射による斉次前合成を厳密に保つ。 -/
lemma dgFunctorGradedPrecompose_map {q x y : D} (k : ℤ) (a : _root_.SerrePositivity.DifferentialGraded.GradedHom A x y k)
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x) :
    (F.map q y).f k (dgGradedPrecompose A D k a s) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A E (q := F.obj q) (x := F.obj x) (y := F.obj y)
        k ((F.map x y).f k a) (F.onClosed.map s) := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose
  have hs := congrArg Subtype.val (F.closedHomEquiv_map s)
  change (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A E _ _ (F.onClosed.map s)).val =
    (F.map q x).f 0 (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D _ _ s).val at hs
  have hm := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.map_compose F (x := q) (y := x) (z := y)
    a (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D _ _ s).val (zero_add k)
  exact hm.trans (congrArg (fun v : _root_.SerrePositivity.DifferentialGraded.GradedHom A (F.obj q) (F.obj x) 0 =>
    _root_.SerrePositivity.DifferentialGraded.compose A ((F.map x y).f k a) v (zero_add k)) hs.symm)

/-- 像の閉射による前合成の cycle は元の閉射の cycle の像で計算できる。 -/
lemma dgGradedPrecompose_image {q x y : D} (k : ℤ)
    (c : _root_.SerrePositivity.DifferentialGraded.GradedHom A (F.obj x) (F.obj y) k)
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A E (q := F.obj q) (x := F.obj x) (y := F.obj y)
      k c (F.onClosed.map s) =
      _root_.SerrePositivity.DifferentialGraded.compose A (D := E) (x := F.obj q) (y := F.obj x) (z := F.obj y)
        c ((F.map q x).f 0 (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D _ _ s).val) (zero_add k) := by
  exact congrArg (fun v : _root_.SerrePositivity.DifferentialGraded.GradedHom A (F.obj q) (F.obj x) 0 =>
    _root_.SerrePositivity.DifferentialGraded.compose A (D := E) (x := F.obj q) (y := F.obj x) (z := F.obj y) c v (zero_add k))
      (congrArg Subtype.val (F.closedHomEquiv_map s))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
