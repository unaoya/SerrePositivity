module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSourceRefinementLinear
public import Mathlib.CategoryTheory.Enriched.Ordinary.Basic
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedEdgeCompositionEquality
/-!
概要：同じ閉前合成の全次数作用を、一般 dg 圏の標準豊穣 Hom 鎖写像へ同定する。
方針：単位テンソル挿入で斉次成分を計算し、実閉辺の一致と等式輸送を保つ。
規約：対象の小ささを仮定しない。使われ方：実 coslice fiber の係数比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory DifferentialGraded
open HomologicalComplex CochainComplex HomComplex
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]
/-- 一般 dg 圏の斉次閉前合成は、同じ標準 Hom 鎖写像の成分そのもの。 -/
lemma dgGradedPrecompose_eq_whisker_f {q x y : D} (k : ℤ) (a : _root_.SerrePositivity.DifferentialGraded.GradedHom R x y k)
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) x) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose R D k a s =
      (eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex R) s (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) y)).f k a := by
  symm
  have hv := congr($(leftUnitor'_inv (x ⟶[_root_.SerrePositivity.DifferentialGraded.Complex R] y) k).hom a)
  change (λ_ (x ⟶[_root_.SerrePositivity.DifferentialGraded.Complex R] y)).inv.f k a =
    ιTensorObj (𝟙_ (_root_.SerrePositivity.DifferentialGraded.Complex R)) (x ⟶[_root_.SerrePositivity.DifferentialGraded.Complex R] y) 0 k k (zero_add k)
      ((1 : R) ⊗ₜ[R] a) at hv
  change (eComp (_root_.SerrePositivity.DifferentialGraded.Complex R) q x y).f k
    ((ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex R) s ⊗ₘ 𝟙 (x ⟶[_root_.SerrePositivity.DifferentialGraded.Complex R] y)).f k
      ((λ_ (x ⟶[_root_.SerrePositivity.DifferentialGraded.Complex R] y)).inv.f k a)) = _
  rw [hv, _root_.SerrePositivity.DifferentialGraded.tensorMap_apply]
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply]
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose, compose, zero_mul, Int.negOnePow_zero, one_smul]
  rfl
/-- 同じ実閉辺と対象・係数の一致は、斉次前合成の異種等号を与える。 -/
lemma dgGradedPrecompose_heq {q x y q' x' y' : D} (k : ℤ)
    (hq : q = q') (hx : x = x') (hy : y = y')
    (a : _root_.SerrePositivity.DifferentialGraded.GradedHom R x y k) (a' : _root_.SerrePositivity.DifferentialGraded.GradedHom R x' y' k) (ha : HEq a a')
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) x)
    (s' : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) q' ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) x')
    (hs : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R D s).edge = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R D s').edge) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose R D k a s) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose R D k a' s') := by
  subst q' x' y'
  cases eq_of_heq ha
  cases _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge_raw_injective R D s s' hs
  rfl
/-- 同じ斉次閉前合成は符号単位スカラー倍と可換。 -/
lemma dgGradedPrecompose_units_smul {q x y : D} (k : ℤ) (c : ℤˣ)
    (a : _root_.SerrePositivity.DifferentialGraded.GradedHom R x y k)
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) x) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose R D k (c • a) s = c • _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose R D k a s := by
  rw [dgGradedPrecompose_eq_whisker_f, dgGradedPrecompose_eq_whisker_f]
  simp only [Units.smul_def, map_zsmul]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
