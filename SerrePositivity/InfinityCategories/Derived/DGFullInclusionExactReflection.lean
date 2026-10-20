module
public import SerrePositivity.InfinityCategories.Derived.FullColimitReflection
public import SerrePositivity.InfinityCategories.DGNerve.FullZeroObject
public import SerrePositivity.InfinityCategories.Stable.ExactFunctor
/-!
概要：充満 dg 部分圏への実関手の完全性を、周囲への包含後の完全性から反映する。
方針：実零頂点と実余極限の境界充填を全包含で反映する。
規約：部分圏の replete 性を要求しない。使われ方：β5 の射影的模型上の tensor 関手。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
/-- 充満 dg 部分圏への関手は、周囲への包含との合成が完全なら完全。 -/
lemma isExactFunctor_of_postcomp_dgFullInclusion (R : Type u) [CommRing R] (E : Type v)
    [DGCategory R E] (P : E → Prop) {X : SSet.{max u v}}
    (F : X ⟶ dgNerve R (DGFullSubcategory E P))
    [IsExactFunctor (F ≫ dgNerve.map (dgFullSubcategoryInclusion R E P))] : IsExactFunctor F where
  preservesZero z hz := by
    have h := IsExactFunctor.preservesZero
      (F := F ≫ dgNerve.map (dgFullSubcategoryInclusion R E P)) z hz
    exact ⟨isInitialVertex_of_fullInclusion R E P _ h.1,
      isTerminalVertex_of_fullInclusion R E P _ h.2⟩
  preservesCofiber t ht := by
    apply isColimitCone_of_fullInclusion R E P (pushoutCocone _)
    exact IsExactFunctor.preservesCofiber
      (F := F ≫ dgNerve.map (dgFullSubcategoryInclusion R E P)) t ht
end SerrePositivity.InfinityCategories
