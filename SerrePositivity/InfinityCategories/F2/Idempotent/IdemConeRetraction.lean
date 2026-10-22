module

public import SerrePositivity.InfinityCategories.F2.Idempotent.WalkingJoinCones

/-!
概要：元の全 Idem は、元の点を右に付けた錐の retract である。
方針：元の恒等図式に吸収元を全ての脚とする余錐を付ける。
規約：元の全 Idem への制限は恒等そのもの。新しい頂点は元の対象へ送る。
使われ方：HTT 4.4.5.9 と Idem の弱可縮性・cofinal 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の恒等図式に、元の吸収元を全ての脚として付けた余錐。 -/
def walkingIdemCocone : Cocone (𝟭 WalkingIdem.{u}) where
  pt := walkingObject
  ι :=
    { app _P := show WithOne PUnit.{u + 1} from walkingAbsorber
      naturality _ _ f := by
        change walkingAbsorber * walkingScalar f = 1 * walkingAbsorber
        rw [walkingAbsorber_mul, one_mul] }

/-- 元の右錐から元の全 Idem への retraction。 -/
def idemConeRetraction : join IdemShape (Δ[0] : SSet.{u}) ⟶ IdemShape :=
  (F1B.kanNerveCoconeEquiv walkingIdemCocone).val

/-- 元の全 Idem への制限は、元の恒等射そのもの。 -/
lemma idemConeRetraction_inl :
    joinInl IdemShape (Δ[0] : SSet.{u}) ≫ idemConeRetraction = 𝟙 IdemShape :=
  (F1B.kanNerveCoconeEquiv walkingIdemCocone).property

/-- 元の新しい頂点への制限は、元の一対象そのもの。 -/
lemma idemConeRetraction_inr :
    joinInr IdemShape (Δ[0] : SSet.{u}) ≫ idemConeRetraction = nervePoint walkingObject :=
  F1B.kanNerveCocone_point walkingIdemCocone

/-- 元の恒等図式から元の定値図式への指定変換の成分は、元の非恒等冪等元。 -/
lemma walkingIdemCocone_leg : walkingIdemCocone.{u}.ι.app walkingObject =
    walkingIdempotent := rfl

end SerrePositivity.InfinityCategories.F2.Idempotent
