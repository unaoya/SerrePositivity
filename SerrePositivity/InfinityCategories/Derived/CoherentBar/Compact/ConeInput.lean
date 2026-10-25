module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.GeneratorClosure
public import SerrePositivity.InfinityCategories.Derived.DGKappaClosedProjectivePretriangulated
public import SerrePositivity.InfinityCategories.Derived.DGKappaClosedProjectiveComparison
public import SerrePositivity.InfinityCategories.Derived.DGKappaClosedPerfectCover
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open SerrePositivity.KST.NonConnective
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (κ : Cardinal.{u}) [Fact κ.IsRegular]

/-- 同じ代表系の K-7 入力。未供給の Hom 保存と covers を引数として保持する。 -/
def dgBarCompactConeInput (hκ : Cardinal.aleph0 < κ)
    (hHom : ∀ x : D, F2.Compact.PreservesKappaFilteredColimits.{u, max (u + 1) v} κ
      (dgHomTargetUnderlyingSpaceInfinity R (ProjectiveDGModules R D)
        (dgBarCompactRepresentableProjective R D x)))
    (hCovers : ∀ y : (dgModuleDerivedInfinityCategory R D) _⦋0⦌,
      F2.Compact.IsKappaCompact.{u, max (u + 1) v} κ y →
        ∃ M : ModuleCategory R D, dgKappaClosedProjectiveObjects R D κ M ∧
          Nonempty (VertexIso (dgConeModuleDerivedVertex R D M) y)) :
    DGKappaConeInput R D κ where
  uncountable := hκ
  regular := Fact.out
  objects := dgKappaClosedProjectiveObjects R D κ
  small := dgKappaClosedProjectiveObjects_small R D κ
  pretriangulated := dgKappaClosedProjectiveObjects_isDGPretriangulated R D hκ Fact.out
  projective := dgKappaClosedProjectiveObjects_projective R D κ
  derivedFullyFaithful := dgKappaClosedProjectiveObjects_derivedFullyFaithful R D κ
  kappaCompact := dgBarCompactClosedProjective_of_hom_preserves R D hHom hκ
  covers := hCovers
  countableClosed := dgKappaClosedProjectiveObjects_countableClosed R D hκ Fact.out
  binaryClosed := dgKappaClosedProjectiveObjects_binaryClosed R D hκ Fact.out
  perfectCovers := dgKappaClosedProjectiveObjects_perfectCovers R D hκ

end SerrePositivity.InfinityCategories
