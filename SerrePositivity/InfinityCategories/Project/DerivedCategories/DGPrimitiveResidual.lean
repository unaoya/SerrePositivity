module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGGradedClosedPrecomposition
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Residual

/-! # 指定された像の原始元との差と補正

概要：元の原始元の像と指定された像の原始元の前合成との差は閉元になる。
方針：微分と前合成・関手性を照合し、追加分母と閉分子による補正を展開する。
規約：指定された原始元を固定する。使われ方：商の指定原始元の相対持ち上げ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory A E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E)

/-- 元の原始元の像と、指定された像の原始元を前合成したものとの差。 -/
def dgPrimitiveResidual {q x y : D} (k : ℤ)
    (c : _root_.SerrePositivity.DifferentialGraded.GradedHom A (F.obj x) (F.obj y) k) (h : _root_.SerrePositivity.DifferentialGraded.GradedHom A q y k)
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x) :
    _root_.SerrePositivity.DifferentialGraded.GradedHom A (F.obj q) (F.obj y) k :=
  (F.map q y).f k h - _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A E
    (q := F.obj q) (x := F.obj x) (y := F.obj y) k c (F.onClosed.map s)

/-- 両原始元の微分が指定通りなら、その相対残差は閉元。 -/
lemma dgPrimitiveResidual_closed {q x y : D} (k : ℤ) (a : _root_.SerrePositivity.DifferentialGraded.GradedHom A x y (k + 1))
    (c : _root_.SerrePositivity.DifferentialGraded.GradedHom A (F.obj x) (F.obj y) k) (h : _root_.SerrePositivity.DifferentialGraded.GradedHom A q y k)
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x)
    (hc : _root_.SerrePositivity.DifferentialGraded.differential A c = (F.map x y).f (k + 1) a)
    (hh : differential A h = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D (k + 1) a s) :
    _root_.SerrePositivity.DifferentialGraded.differential A (dgPrimitiveResidual A D E F k c h s) = 0 := by
  have hp := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose_d A E
    (q := F.obj q) (x := F.obj x) (y := F.obj y) k (k + 1) rfl c (F.onClosed.map s)
  change differential A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A E (q := F.obj q) (x := F.obj x) (y := F.obj y)
    k c (F.onClosed.map s)) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A E (q := F.obj q) (x := F.obj x) (y := F.obj y)
      (k + 1) (_root_.SerrePositivity.DifferentialGraded.differential A c) (F.onClosed.map s) at hp
  rw [dgPrimitiveResidual, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.differential_sub, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.map_differential F, hh,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorGradedPrecompose_map, hp, hc, sub_self]

/-- 補正した元の微分は、指定された二分母の合成による前合成になる。 -/
lemma dgPrimitiveCorrection_d {p q x y : D} (k : ℤ) (a : _root_.SerrePositivity.DifferentialGraded.GradedHom A x y (k + 1))
    (h : _root_.SerrePositivity.DifferentialGraded.GradedHom A q y k) (e : _root_.SerrePositivity.DifferentialGraded.GradedHom A p y k)
    (r : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) p ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q)
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x)
    (hh : differential A h = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D (k + 1) a s)
    (he : _root_.SerrePositivity.DifferentialGraded.differential A e = 0) :
    differential A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D k h r - e) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D (k + 1) a (r ≫ s) := by
  have hp := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose_d A D k (k + 1) rfl h r
  change differential A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D k h r) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D (k + 1) (differential A h) r at hp
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.differential_sub, hp, hh, he, sub_zero, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose_comp]

/-- 補正後の残差は、元の残差の前合成から閉分子の像を引いたもの。 -/
lemma dgPrimitiveCorrection_residual {p q x y : D} (k : ℤ)
    (c : _root_.SerrePositivity.DifferentialGraded.GradedHom A (F.obj x) (F.obj y) k) (h : _root_.SerrePositivity.DifferentialGraded.GradedHom A q y k) (e : _root_.SerrePositivity.DifferentialGraded.GradedHom A p y k)
    (r : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) p ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q)
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x) :
    dgPrimitiveResidual A D E F k c (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D k h r - e) (r ≫ s) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A E (q := F.obj p) (x := F.obj q) (y := F.obj y)
        k (dgPrimitiveResidual A D E F k c h s) (F.onClosed.map r) -
        (F.map p y).f k e := by
  unfold dgPrimitiveResidual
  rw [map_sub, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorGradedPrecompose_map, Functor.map_comp,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose_sub, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose_comp]
  abel

end SerrePositivity.InfinityCategories.Project.DerivedCategories
