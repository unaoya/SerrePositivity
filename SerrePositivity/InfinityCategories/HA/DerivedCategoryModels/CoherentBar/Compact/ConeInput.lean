module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.GeneratorClosure
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaClosedProjectivePretriangulated
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaClosedProjectiveComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaClosedPerfectCover
/-!
概要：選択済みの同じ代表系について、Hom 保存と covers から K-7 入力を組み立てる。
方針：前三角性・射影性・全写像空間の充満忠実性・直和閉性は既存の実証拠を使う。
規約：代表 Hom の全 native 保存と covers は明示入力。比較の実値を仮定せず捏造しない。
使われ方：coherent C1 と D-e の被覆が供給された後の最終代入。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory DifferentialGraded SSet
open _root_.SerrePositivity.KST.NonConnective
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  (κ : Cardinal.{u}) [Fact κ.IsRegular]

/-- 同じ代表系の K-7 入力。未供給の Hom 保存と covers を引数として保持する。 -/
def dgBarCompactConeInput (hκ : Cardinal.aleph0 < κ)
    (hHom : ∀ x : D, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesKappaFilteredColimits.{u, max (u + 1) v} κ
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetUnderlyingSpaceInfinity R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D)
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactRepresentableProjective R D x)))
    (hCovers : ∀ y : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D) _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, max (u + 1) v} κ y →
        ∃ M : ModuleCategory R D, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects R D κ M ∧
          Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (dgConeModuleDerivedVertex R D M) y)) :
    DGKappaConeInput R D κ where
  uncountable := hκ
  regular := Fact.out
  objects := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects R D κ
  small := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects_small R D κ
  pretriangulated := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects_isDGPretriangulated R D hκ Fact.out
  projective := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects_projective R D κ
  derivedFullyFaithful := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects_derivedFullyFaithful R D κ
  kappaCompact := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactClosedProjective_of_hom_preserves R D hHom hκ
  covers := hCovers
  countableClosed := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects_countableClosed R D hκ Fact.out
  binaryClosed := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects_binaryClosed R D hκ Fact.out
  perfectCovers := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects_perfectCovers R D hκ

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
