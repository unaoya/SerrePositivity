module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGKappaSphereClosureComparison

/-!
概要：B′ の sphere-only 閉包を使う無条件 cone 入力を公開する。
方針：新族の被覆・perfect telescope 被覆と実閉性を正本の全フィールドへ渡す。
規約：旧 dgKappaConeInput_unconditional を削除・改名・変更しない。
使われ方：K-B3 の新段提供者と D-S の閉包関手性・懸垂作用。
-/
@[expose] public noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory DifferentialGraded SSet
open _root_.SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  (κ : Cardinal.{u}) [Fact κ.IsRegular] (hκ : Cardinal.aleph0 < κ)

/-- D-2：perfect 基底を含まない、新しい実閉包模型の無条件 cone 入力。 -/
def dgKappaConeInput_unconditional' : DGKappaConeInput R D κ where
  uncountable := hκ
  regular := Fact.out
  objects := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects R D κ
  small := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects_small R D κ
  pretriangulated := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects_isDGPretriangulated R D hκ Fact.out
  projective := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects_projective R D κ
  derivedFullyFaithful := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects_derivedFullyFaithful R D hκ Fact.out
  kappaCompact := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects_isKappaCompact R D hκ Fact.out
  covers := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosure_covers_unconditional R D hκ Fact.out
  countableClosed := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects_countableClosed R D hκ Fact.out
  binaryClosed := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects_binaryClosed R D hκ Fact.out
  perfectCovers := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects_perfectCovers R D hκ Fact.out

lemma dgKappaConeInput_unconditional'_objects :
    (dgKappaConeInput_unconditional' R D κ hκ).objects = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects R D κ := rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
