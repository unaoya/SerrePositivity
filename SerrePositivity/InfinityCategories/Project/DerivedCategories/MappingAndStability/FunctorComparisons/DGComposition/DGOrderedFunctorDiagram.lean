module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGStrictNatTransAlgebra
/-!
概要：順序で添字付けた厳密 dg 関手図式と、全斉次射の相間輸送を構成する。
方針：実閉零成分と全 Hom 自然性、元の単位・合成則を使う。
規約：dg nerve の変換の等式は別途実単体で証明する。
使われ方：一般 kernel 比較の恒等・合成 coherence。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w t
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
/-- 全 Hom に自然な変換と恒等・合成の整合性を持つ、順序添字の dg 関手図式。 -/
structure DGOrderedFunctorDiagram (R : Type u) [CommRing R]
    (C : Type v) (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]
    (I : Type t) [Preorder I] where
  /-- 各相の元の dg 関手。 -/
  obj : I → _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E
  /-- 昇順の相の間の厳密 dg 自然変換。 -/
  map : ∀ p q : I, p ≤ q → _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans (obj p) (obj q)
  /-- 同じ相の変換は元の厳密恒等。 -/
  map_refl : ∀ p, map p p le_rfl = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransId (obj p)
  /-- 三相の変換は元の通常順合成と整合する。 -/
  map_trans : ∀ p q r (hpq : p ≤ q) (hqr : q ≤ r),
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp (map p q hpq) (map q r hqr) = map p r (hpq.trans hqr)
namespace DGOrderedFunctorDiagram
variable {R : Type u} [CommRing R] {C : Type v} {E : Type w}
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] {I : Type t} [Preorder I]
  (d : DGOrderedFunctorDiagram R C E I)
/-- 昇順の相の間の全斉次射を、同じ閉零成分と元の dg 作用で写す。 -/
def transition {x y : C} {k : ℤ} (p q : I) (hpq : p ≤ q) (f : _root_.SerrePositivity.DifferentialGraded.GradedHom R x y k) :
    _root_.SerrePositivity.DifferentialGraded.GradedHom R ((d.obj p).obj x) ((d.obj q).obj y) k :=
  _root_.SerrePositivity.DifferentialGraded.compose R ((d.map p q hpq).app y).val (((d.obj p).map x y).f k f) (add_zero k)
/-- 相間輸送は零を保つ。 -/
lemma transition_zero {x y : C} {k : ℤ} (p q : I) (hpq : p ≤ q) :
    d.transition p q hpq (0 : _root_.SerrePositivity.DifferentialGraded.GradedHom R x y k) = 0 := by
  simp only [transition, map_zero, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero]
/-- 相間輸送は差を保つ。 -/
lemma transition_sub {x y : C} {k : ℤ} (p q : I) (hpq : p ≤ q)
    (f g : _root_.SerrePositivity.DifferentialGraded.GradedHom R x y k) :
    d.transition p q hpq (f - g) = d.transition p q hpq f - d.transition p q hpq g := by
  simp only [transition, map_sub, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sub_right]
/-- 相間輸送は整数の符号スカラーを保つ。 -/
lemma transition_smul {x y : C} {k : ℤ} (p q : I) (hpq : p ≤ q)
    (a : ℤˣ) (f : _root_.SerrePositivity.DifferentialGraded.GradedHom R x y k) :
    d.transition p q hpq (a • f) = a • d.transition p q hpq f := by
  unfold transition
  have hs : ((d.obj p).map x y).f k (a • f) = a • ((d.obj p).map x y).f k f := by
    simp only [Units.smul_def, map_zsmul]
  rw [hs]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_units_smul_right a _ _ (add_zero k)
/-- 相間輸送は有限和を保つ。 -/
lemma transition_sum {ι : Type*} {x y : C} {k : ℤ} (p q : I) (hpq : p ≤ q)
    (S : Finset ι) (f : ι → _root_.SerrePositivity.DifferentialGraded.GradedHom R x y k) :
    d.transition p q hpq (∑ i ∈ S, f i) = ∑ i ∈ S, d.transition p q hpq (f i) := by
  simp only [transition, map_sum, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sum_right]
/-- 相間輸送は全整数次数で微分と可換。 -/
lemma transition_differential {x y : C} {k : ℤ} (p q : I) (hpq : p ≤ q)
    (f : _root_.SerrePositivity.DifferentialGraded.GradedHom R x y k) :
    d.transition p q hpq (_root_.SerrePositivity.DifferentialGraded.differential R f) = _root_.SerrePositivity.DifferentialGraded.differential R (d.transition p q hpq f) := by
  unfold transition
  have hc : _root_.SerrePositivity.DifferentialGraded.differential R ((d.map p q hpq).app y).val = 0 := (d.map p q hpq).app y |>.property
  rw [_root_.SerrePositivity.DifferentialGraded.differential_compose]
  simp only [hc, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose, Int.negOnePow_zero, one_smul, zero_add]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.map_differential]
/-- 同じ相の間の輸送は元の単位を保つ。 -/
lemma transition_unit (p : I) (x : C) :
    d.transition p p le_rfl (_root_.SerrePositivity.DifferentialGraded.unitElement R x).val = (_root_.SerrePositivity.DifferentialGraded.unitElement R ((d.obj p).obj x)).val := by
  unfold transition
  rw [d.map_refl, _root_.SerrePositivity.DifferentialGraded.DGFunctor.map_unitElement]
  exact _root_.SerrePositivity.DifferentialGraded.unit_compose R _
/-- 三相の間の輸送は元の斉次合成を保つ。 -/
lemma transition_compose {x y z : C} {i j k : ℤ} (p q r : I)
    (hpq : p ≤ q) (hqr : q ≤ r) (g : _root_.SerrePositivity.DifferentialGraded.GradedHom R y z j) (f : _root_.SerrePositivity.DifferentialGraded.GradedHom R x y i)
    (hk : i + j = k) :
    d.transition p r (hpq.trans hqr) (_root_.SerrePositivity.DifferentialGraded.compose R g f hk) =
      _root_.SerrePositivity.DifferentialGraded.compose R (d.transition q r hqr g) (d.transition p q hpq f) hk := by
  have hc := congrArg
    (fun a : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans (d.obj p) (d.obj r) => (a.app z).val)
    (d.map_trans p q r hpq hqr)
  change _root_.SerrePositivity.DifferentialGraded.compose R ((d.map q r hqr).app z).val ((d.map p q hpq).app z).val
    (zero_add 0) = ((d.map p r (hpq.trans hqr)).app z).val at hc
  have ht := (d.map p q hpq).transition_compose 0 1 1
    (by decide) (by decide) g f hk
  change _root_.SerrePositivity.DifferentialGraded.compose R ((d.map p q hpq).app z).val
      (((d.obj p).map x z).f k (_root_.SerrePositivity.DifferentialGraded.compose R g f hk)) (add_zero k) =
    _root_.SerrePositivity.DifferentialGraded.compose R (((d.obj q).map y z).f j g)
      (d.transition p q hpq f) hk at ht
  unfold transition
  rw [← hc]
  calc
    _ = _root_.SerrePositivity.DifferentialGraded.compose R ((d.map q r hqr).app z).val
        (_root_.SerrePositivity.DifferentialGraded.compose R ((d.map p q hpq).app z).val
          (((d.obj p).map x z).f k (_root_.SerrePositivity.DifferentialGraded.compose R g f hk)) (add_zero k)) (add_zero k) :=
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.compose_assoc_of_sum _ _ _ (add_zero k) (zero_add 0) (add_zero k)).symm
    _ = _root_.SerrePositivity.DifferentialGraded.compose R ((d.map q r hqr).app z).val
        (_root_.SerrePositivity.DifferentialGraded.compose R (((d.obj q).map y z).f j g) (d.transition p q hpq f) hk)
        (add_zero k) := by rw [ht]
    _ = _ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.compose_assoc_of_sum _ _ _ hk (add_zero j) (add_zero k)
end DGOrderedFunctorDiagram
end SerrePositivity.InfinityCategories.Project.DerivedCategories
