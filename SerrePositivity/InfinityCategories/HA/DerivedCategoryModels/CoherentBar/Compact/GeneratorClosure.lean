module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.ProjectiveHomCriterion
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaClosedCompactGeneratorCriterion
/-!
概要：全 native 図式での代表 Hom の保存を、七入力の native κ-compact 性へ接続する。
方針：同じ射影的代表で compact 性を判定し、既存の一般生成元判定を適用する。
規約：Hom 保存の証明は明示入力。coherent C1 自体の証明とは区別する。
使われ方：c2 の評価交換が届いた後の c6・c7 の接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}}
  (hHom : ∀ x : D, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesKappaFilteredColimits.{u, max (u + 1) v} κ
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetUnderlyingSpaceInfinity R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactRepresentableProjective R D x)))
include hHom

/-- 代表そのものの全 Hom 保存から、同じ実分解頂点の native compact 性を得る。 -/
lemma dgBarCompactRepresentable_of_hom_preserves (x : D) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact R D κ (ForgetEnrichment.of (Complex R) (representable R x)) :=
  (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactRepresentable_iff_hom_preserves R D κ x).mpr (hHom x)

/-- 同じ代表の全整数 shift は、全 native 図式について κ-compact。 -/
lemma dgBarCompactRepresentableShift_of_hom_preserves (x : D) (s : ℤ) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact R D κ
      ((ForgetEnrichment.of (Complex R) (representable R x))⟦s⟧) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact_shift R D (dgBarCompactRepresentable_of_hom_preserves R D hHom x) s

variable [Fact κ.IsRegular] (hκ : Cardinal.aleph0 < κ)
include hκ

/-- κ 未満の sphere-free 基底に、元の native compact 条件を供給する。 -/
lemma dgBarCompactSphereFree_of_hom_preserves (i : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaSphereFreeIndex D κ) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact R D κ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereFreeModule R D i) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereFreeModule_isKappaCompact_of_generators R D hκ
    (dgBarCompactRepresentable_of_hom_preserves R D hHom) i

/-- 七入力の一般判定を通し、選んだ全閉包代表の native compact 性を得る。 -/
lemma dgBarCompactClosedProjective_of_hom_preserves
    (M : ModuleCategory R D) (hM : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects R D κ M) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact R D κ M :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects_isKappaCompact_of_generators R D hκ
    (dgBarCompactRepresentable_of_hom_preserves R D hHom) M hM

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
