module

public import SerrePositivity.KST.NonConnective.DGKappaSplitInclusions
public import SerrePositivity.KST.NonConnective.DGSumPairProjection

/-!
概要：同じ dg cone の id ⊕ T から id・T への、全 Hom end 内の実閉射影。
方針：実二項 dg 直和の全斉次射影を同じ充満部分圏へ制限する。
規約：選んだ同じ直和を使い、零次自然変換だけで代用しない。
使われ方：Perf の全 native 作用へ渡す分裂 cofiber 族。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 同じ dg 関手 Hom end 内の id 成分への実閉射影。 -/
def dgKappaSplitHeadProjection :
    ForgetEnrichment.of (Complex R) (dgKappaSwindleSource R D I) ⟶
      ForgetEnrichment.of (Complex R) (DGFunctor.id (A := R) (DGKappaCone R D I)) :=
  dgFunctorClosedHomFromFamily R (DGKappaCone R D I) (DGKappaCone R D I)
    (dgKappaSwindleSource R D I) (DGFunctor.id (A := R) (DGKappaCone R D I))
    (fun X ↦ dgSumPairProjection R D (dgSwindleSummand R D) WalkingPair.left X.val)
    (fun X Y ↦ dgSumPairProjection_naturality R D (dgSwindleSummand R D)
      WalkingPair.left X.val Y.val)

/-- 同じ dg 関手 Hom end 内の T 成分への実閉射影。 -/
def dgKappaSplitTailProjection :
    ForgetEnrichment.of (Complex R) (dgKappaSwindleSource R D I) ⟶
      ForgetEnrichment.of (Complex R) (dgKappaConeCountableSum R D I) :=
  dgFunctorClosedHomFromFamily R (DGKappaCone R D I) (DGKappaCone R D I)
    (dgKappaSwindleSource R D I) (dgKappaConeCountableSum R D I)
    (fun X ↦ dgSumPairProjection R D (dgSwindleSummand R D) WalkingPair.right X.val)
    (fun X Y ↦ dgSumPairProjection_naturality R D (dgSwindleSummand R D)
      WalkingPair.right X.val Y.val)

end SerrePositivity.KST.NonConnective
