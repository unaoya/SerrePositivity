module
public import SerrePositivity.InfinityCategories.Derived.DGSemifreeHomTargetSpaceComparison
public import SerrePositivity.InfinityCategories.Derived.DGCosliceYonedaOppositeComparison
public import SerrePositivity.InfinityCategories.F1B.Compact.RepresentableCoslice
public import SerrePositivity.InfinityCategories.F2.Compact.Preservation
/-!
概要：半自由加群の native κ-compact 性を全 Hom 空間関手の余極限保存で判定する。
方針：同じ coslice の分類比較を介し、実 Hom の全関手同型を共変代表へ合成する。
規約：試験対象は全 native κ-filtered 図式。strict 図式への制限は行わない。
使われ方：coherent bar の評価比較を c2 の定義へ代入する消費入口。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

/-- 任意の dg 模型の実 Hom 空間関手を、同じ頂点の共変代表へ比較する。 -/
def dgBarCompactHomIso (C : Type (max (u + 1) v)) [DGCategory R C] (x : C) :
    FunctorIso (dgHomTargetUnderlyingSpaceInfinity R C x)
      (covariantRepresentableInfinity (C := dgNerve R C) (Simplex.vertex (A := R) x)) :=
  dgHomTargetSpaceComparisonIso R C x ≪≫
    dgCosliceYonedaClassificationIso (dgNerve R C) (Simplex.vertex (A := R) x) ≪≫
    (F2.Compact.covariantRepresentableInfinity_cosliceIso (C := dgNerve R C)
      (Simplex.vertex (A := R) x)).symm

/-- 全 native 図式での実 Hom 保存と同じ頂点の compact 性の一般判定。 -/
lemma dgBarCompact_iff_hom_preserves (C : Type (max (u + 1) v)) [DGCategory R C]
    (κ : Cardinal.{u}) (x : C) :
    F2.Compact.IsKappaCompact.{u, max (u + 1) v} (C := dgNerve R C) κ
        (Simplex.vertex (A := R) x) ↔
      F2.Compact.PreservesKappaFilteredColimits.{u, max (u + 1) v} κ
        (dgHomTargetUnderlyingSpaceInfinity R C x) := by
  constructor
  · intro h
    exact h.of_functorIso (dgBarCompactHomIso R C x).symm
  · intro h
    exact h.of_functorIso (dgBarCompactHomIso R C x)

/-- 実半自由 Hom の全空間関手と compact 性の定義にある元の共変代表の比較。 -/
def dgBarCompactNativeHomIso (P : SemifreeDGModules R D) :
    FunctorIso (dgSemifreeDerivedHomTargetSpaceInfinity R D P)
      (covariantRepresentableInfinity (dgSemifreeHomVertex R D P)) := by
  have e := dgSemifreeDerivedHomTargetF1SpaceIso R D P
  rw [dgSemifreeHomTargetF1SpaceInfinity_eq_yoneda] at e
  exact e ≪≫ dgCosliceYonedaClassificationIso (dgModuleDerivedInfinityCategory R D)
      (dgSemifreeHomVertex R D P) ≪≫
    (F2.Compact.covariantRepresentableInfinity_cosliceIso
      (dgSemifreeHomVertex R D P)).symm

/-- 全 native 図式での実 Hom 空間の余極限保存は、同じ頂点の native compact 性と同値。 -/
lemma dgBarCompact_iff_nativeHom_preserves (κ : Cardinal.{u}) (P : SemifreeDGModules R D) :
    F2.Compact.IsKappaCompact.{u, max (u + 1) v}
        κ (dgSemifreeHomVertex R D P) ↔
      F2.Compact.PreservesKappaFilteredColimits.{u, max (u + 1) v}
        κ (dgSemifreeDerivedHomTargetSpaceInfinity R D P) := by
  constructor
  · intro h
    exact h.of_functorIso (dgBarCompactNativeHomIso R D P).symm
  · intro h
    exact h.of_functorIso (dgBarCompactNativeHomIso R D P)

end SerrePositivity.InfinityCategories
