module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPrimitiveResidual

/-! # 相対原始元と比較境界の閉分母による細分

概要：元の原始元と商内の比較境界を同じ閉射で前合成し、相対微分式を保つ。
方針：前合成の微分・合成・関手性を残差の補正式と接続する。
規約：指定された商の原始元は変更しない。使われ方：有限族の共通実分母への帰納。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
  (E : Type w) [DGCategory A E] (F : DGFunctor A D E)

/-- 元の原始元を追加閉射で前合成すると、残差も同じ像の閉射で前合成される。 -/
lemma dgPrimitiveResidual_refine {p q x y : D} (k : ℤ)
    (c : GradedHom A (F.obj x) (F.obj y) k) (h : GradedHom A q y k)
    (r : ForgetEnrichment.of (Complex A) p ⟶ ForgetEnrichment.of (Complex A) q)
    (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPrimitiveResidual A D E F k c (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D k h r) (r ≫ s) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A E (q := F.obj p) (x := F.obj q) (y := F.obj y)
        k (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPrimitiveResidual A D E F k c h s) (F.onClosed.map r) := by
  simpa only [sub_zero, map_zero] using
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPrimitiveCorrection_residual A D E F k c h (0 : GradedHom A p y k) r s

/-- 指定原始元を前合成してから相対比較しても、分母を合成した比較と一致する。 -/
lemma dgPrimitiveResidual_nested {p q x y : D} (k : ℤ)
    (c : GradedHom A (F.obj x) (F.obj y) k) (h : GradedHom A p y k)
    (r : ForgetEnrichment.of (Complex A) p ⟶ ForgetEnrichment.of (Complex A) q)
    (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPrimitiveResidual A D E F (q := p) (x := q) (y := y) k
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A E (q := F.obj q) (x := F.obj x) (y := F.obj y)
        k c (F.onClosed.map s)) h r =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPrimitiveResidual A D E F k c h (r ≫ s) := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPrimitiveResidual
  rw [Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose_comp]

/-- 原始元と比較境界の両微分式は、追加閉分母の前合成で同時に保たれる。 -/
lemma dgRelativePrimitiveWitness_refine {p q x y : D} (k : ℤ)
    (a : GradedHom A x y (k + 1)) (c : GradedHom A (F.obj x) (F.obj y) k)
    (h : GradedHom A q y k) (b : GradedHom A (F.obj q) (F.obj y) (k - 1))
    (r : ForgetEnrichment.of (Complex A) p ⟶ ForgetEnrichment.of (Complex A) q)
    (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x)
    (hh : differential A h = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D (k + 1) a s)
    (hb : (homObject A E (F.obj q) (F.obj y)).d (k - 1) k b =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPrimitiveResidual A D E F k c h s) :
    differential A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D k h r) =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D (k + 1) a (r ≫ s) ∧
      (homObject A E (F.obj p) (F.obj y)).d (k - 1) k
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A E (q := F.obj p) (x := F.obj q) (y := F.obj y)
          (k - 1) b (F.onClosed.map r)) =
            _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPrimitiveResidual A D E F k c (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D k h r) (r ≫ s) := by
  constructor
  · have hp := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose_d A D k (k + 1) rfl h r
    change differential A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D k h r) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D (k + 1) (differential A h) r at hp
    rw [hp, hh, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose_comp]
  · have hp := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose_d A E (q := F.obj p) (x := F.obj q) (y := F.obj y)
      (k - 1) k (by omega) b (F.onClosed.map r)
    exact hp.trans ((congrArg (fun z : GradedHom A (F.obj q) (F.obj y) k =>
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A E (q := F.obj p) (x := F.obj q) (y := F.obj y)
        k z (F.onClosed.map r)) hb).trans (dgPrimitiveResidual_refine A D E F k c h r s).symm)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
