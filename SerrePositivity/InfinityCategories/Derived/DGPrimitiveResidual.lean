module
public import SerrePositivity.InfinityCategories.Derived.DGGradedClosedPrecomposition
public import SerrePositivity.InfinityCategories.DGNerve.Residual

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
  (E : Type w) [DGCategory A E] (F : DGFunctor A D E)

/-- 元の原始元の像と、指定された像の原始元を前合成したものとの差。 -/
def dgPrimitiveResidual {q x y : D} (k : ℤ)
    (c : GradedHom A (F.obj x) (F.obj y) k) (h : GradedHom A q y k)
    (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x) :
    GradedHom A (F.obj q) (F.obj y) k :=
  (F.map q y).f k h - dgGradedPrecompose A E
    (q := F.obj q) (x := F.obj x) (y := F.obj y) k c (F.onClosed.map s)

/-- 両原始元の微分が指定通りなら、その相対残差は閉元。 -/
lemma dgPrimitiveResidual_closed {q x y : D} (k : ℤ) (a : GradedHom A x y (k + 1))
    (c : GradedHom A (F.obj x) (F.obj y) k) (h : GradedHom A q y k)
    (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x)
    (hc : differential A c = (F.map x y).f (k + 1) a)
    (hh : differential A h = dgGradedPrecompose A D (k + 1) a s) :
    differential A (dgPrimitiveResidual A D E F k c h s) = 0 := by
  have hp := dgGradedPrecompose_d A E
    (q := F.obj q) (x := F.obj x) (y := F.obj y) k (k + 1) rfl c (F.onClosed.map s)
  change differential A (dgGradedPrecompose A E (q := F.obj q) (x := F.obj x) (y := F.obj y)
    k c (F.onClosed.map s)) =
    dgGradedPrecompose A E (q := F.obj q) (x := F.obj x) (y := F.obj y)
      (k + 1) (differential A c) (F.onClosed.map s) at hp
  rw [dgPrimitiveResidual, differential_sub, ← map_differential F, hh,
    dgFunctorGradedPrecompose_map, hp, hc, sub_self]

/-- 補正した元の微分は、指定された二分母の合成による前合成になる。 -/
lemma dgPrimitiveCorrection_d {p q x y : D} (k : ℤ) (a : GradedHom A x y (k + 1))
    (h : GradedHom A q y k) (e : GradedHom A p y k)
    (r : ForgetEnrichment.of (Complex A) p ⟶ ForgetEnrichment.of (Complex A) q)
    (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x)
    (hh : differential A h = dgGradedPrecompose A D (k + 1) a s)
    (he : differential A e = 0) :
    differential A (dgGradedPrecompose A D k h r - e) =
      dgGradedPrecompose A D (k + 1) a (r ≫ s) := by
  have hp := dgGradedPrecompose_d A D k (k + 1) rfl h r
  change differential A (dgGradedPrecompose A D k h r) =
    dgGradedPrecompose A D (k + 1) (differential A h) r at hp
  rw [differential_sub, hp, hh, he, sub_zero, dgGradedPrecompose_comp]

/-- 補正後の残差は、元の残差の前合成から閉分子の像を引いたもの。 -/
lemma dgPrimitiveCorrection_residual {p q x y : D} (k : ℤ)
    (c : GradedHom A (F.obj x) (F.obj y) k) (h : GradedHom A q y k) (e : GradedHom A p y k)
    (r : ForgetEnrichment.of (Complex A) p ⟶ ForgetEnrichment.of (Complex A) q)
    (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x) :
    dgPrimitiveResidual A D E F k c (dgGradedPrecompose A D k h r - e) (r ≫ s) =
      dgGradedPrecompose A E (q := F.obj p) (x := F.obj q) (y := F.obj y)
        k (dgPrimitiveResidual A D E F k c h s) (F.onClosed.map r) -
        (F.map p y).f k e := by
  unfold dgPrimitiveResidual
  rw [map_sub, dgFunctorGradedPrecompose_map, Functor.map_comp,
    dgGradedPrecompose_sub, dgGradedPrecompose_comp]
  abel

end SerrePositivity.InfinityCategories
