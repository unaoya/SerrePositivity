module
public import SerrePositivity.InfinityCategories.Derived.DGKappaSphereClosureComparison

/-!
概要：B′ の sphere-only 閉包を使う無条件 cone 入力を公開する。
方針：新族の被覆・perfect telescope 被覆と実閉性を正本の全フィールドへ渡す。
規約：旧 dgKappaConeInput_unconditional を削除・改名・変更しない。
使われ方：K-B3 の新段提供者と D-S の閉包関手性・懸垂作用。
-/
@[expose] public noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (κ : Cardinal.{u}) [Fact κ.IsRegular] (hκ : Cardinal.aleph0 < κ)

/-- D-2：perfect 基底を含まない、新しい実閉包模型の無条件 cone 入力。 -/
def dgKappaConeInput_unconditional' : DGKappaConeInput R D κ where
  uncountable := hκ
  regular := Fact.out
  objects := dgKappaSphereClosureObjects R D κ
  small := dgKappaSphereClosureObjects_small R D κ
  pretriangulated := dgKappaSphereClosureObjects_isDGPretriangulated R D hκ Fact.out
  projective := dgKappaSphereClosureObjects_projective R D κ
  derivedFullyFaithful := dgKappaSphereClosureObjects_derivedFullyFaithful R D hκ Fact.out
  kappaCompact := dgKappaSphereClosureObjects_isKappaCompact R D hκ Fact.out
  covers := dgKappaSphereClosure_covers_unconditional R D hκ Fact.out
  countableClosed := dgKappaSphereClosureObjects_countableClosed R D hκ Fact.out
  binaryClosed := dgKappaSphereClosureObjects_binaryClosed R D hκ Fact.out
  perfectCovers := dgKappaSphereClosureObjects_perfectCovers R D hκ Fact.out

lemma dgKappaConeInput_unconditional'_objects :
    (dgKappaConeInput_unconditional' R D κ hκ).objects = dgKappaSphereClosureObjects R D κ := rfl

end SerrePositivity.InfinityCategories
