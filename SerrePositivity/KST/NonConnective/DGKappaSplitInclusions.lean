module

public import SerrePositivity.KST.NonConnective.DGSwindleInputIso
public import SerrePositivity.KST.NonConnective.DGSumFamilyInclusion

/-!
概要：同じ dg cone の id・T から id ⊕ T への、全 Hom end 内の実閉射。
方針：直和の全斉次自然性を関手圏の end 普遍性へ渡す。
規約：可逆射の core に制限せず、元の非可逆な両注入も保持する。
使われ方：全 native Perf 作用での実分裂 cofiber 族。
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

/-- 同じ実左注入の全 Hom 自然性。 -/
lemma dgKappaSplitHead_naturality (X Y : DGKappaCone R D I) :
    (DGFunctor.id (A := R) (DGKappaCone R D I)).map X Y ≫
      eHomWhiskerLeft (Complex R) X.val
        (coprod.inl : Y.val ⟶ Y.val ⨿ dgCountableSumObj R D Y.val) =
    (dgKappaSwindleSource R D I).map X Y ≫
      eHomWhiskerRight (Complex R)
        (coprod.inl : X.val ⟶ X.val ⨿ dgCountableSumObj R D X.val)
        (Y.val ⨿ dgCountableSumObj R D Y.val) := by
  exact (dgSumFamilyHom_injection R D (dgSwindleSummand R D) X.val Y.val
    WalkingPair.left).symm

/-- 同じ実右注入の全 Hom 自然性。 -/
lemma dgKappaSplitTail_naturality (X Y : DGKappaCone R D I) :
    (dgKappaConeCountableSum R D I).map X Y ≫
      eHomWhiskerLeft (Complex R) (dgCountableSumObj R D X.val)
        (coprod.inr : dgCountableSumObj R D Y.val ⟶
          Y.val ⨿ dgCountableSumObj R D Y.val) =
    (dgKappaSwindleSource R D I).map X Y ≫
      eHomWhiskerRight (Complex R)
        (coprod.inr : dgCountableSumObj R D X.val ⟶
          X.val ⨿ dgCountableSumObj R D X.val)
        (Y.val ⨿ dgCountableSumObj R D Y.val) := by
  exact (dgSumFamilyHom_injection R D (dgSwindleSummand R D) X.val Y.val
    WalkingPair.right).symm

/-- id から id ⊕ T への、同じ dg 関手圏の全 Hom end 内の実閉左注入。 -/
def dgKappaSplitHead :
    ForgetEnrichment.of (Complex R) (DGFunctor.id (A := R) (DGKappaCone R D I)) ⟶
      ForgetEnrichment.of (Complex R) (dgKappaSwindleSource R D I) :=
  dgFunctorClosedHomFromFamily R (DGKappaCone R D I) (DGKappaCone R D I)
    (DGFunctor.id (A := R) (DGKappaCone R D I)) (dgKappaSwindleSource R D I)
    (fun X ↦ (coprod.inl : X.val ⟶ X.val ⨿ dgCountableSumObj R D X.val))
    (dgKappaSplitHead_naturality R D I)

/-- T から id ⊕ T への、同じ dg 関手圏の全 Hom end 内の実閉右注入。 -/
def dgKappaSplitTail :
    ForgetEnrichment.of (Complex R) (dgKappaConeCountableSum R D I) ⟶
      ForgetEnrichment.of (Complex R) (dgKappaSwindleSource R D I) :=
  dgFunctorClosedHomFromFamily R (DGKappaCone R D I) (DGKappaCone R D I)
    (dgKappaConeCountableSum R D I) (dgKappaSwindleSource R D I)
    (fun X ↦ (coprod.inr : dgCountableSumObj R D X.val ⟶
      X.val ⨿ dgCountableSumObj R D X.val)) (dgKappaSplitTail_naturality R D I)

end SerrePositivity.KST.NonConnective
