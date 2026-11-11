module
public import SerrePositivity.KST.SConstruction.ClosedPredicateOperations
public import SerrePositivity.KST.SConstruction.GappedPushoutPreservation

/-! # S_n の全成分が閉じた部分圏に入る条件
概要：全 Ar 成分の所属条件を S_n C 上の閉じた安定頂点条件にする。
方針：完全な評価による逆像を全ての Ar 頂点について交差させる。
規約：S_n 全体の高次単体を対象とする。使われ方：相対加法性の有限反復。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 任意個の安定な閉性条件の交わりも同じ閉性を持つ。 -/
def ClosedStablePredicate.iInter {X : StableModel.{u}} {I : Type v}
    (P : I → ClosedStablePredicate X) : ClosedStablePredicate X where
  predicate x := ∀ i, (P i).predicate x
  of_iso hx e i := (P i).of_iso (hx i) e
  zero_mem hz i := (P i).zero_mem hz
  pushout_mem F hF h00 h10 h01 i := (P i).pushout_mem F hF (h00 i) (h10 i) (h01 i)
  pullback_mem F hF h10 h01 h11 i := (P i).pullback_mem F hF (h10 i) (h01 i) (h11 i)

/-- gapped 図式の任意の Ar 成分の評価は完全関手。 -/
def sStableEvaluation (n : ℕ) (X : StableModel.{u}) (a : (arNerve n) _⦋0⦌) :
    sStableModel n X ⟶ X :=
  ⟨(gappedSubcomplex n X.carrier).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a,
    ((gappedInclusion_preservesSConstructionData n X.carrier).comp
      (evaluateFunctorAt_preservesSConstructionData a)).toCofiberData⟩

/-- S_n C の全 Ar 成分が元の閉じた部分圏に入る閉性条件。 -/
def sClosedPredicate {X : StableModel.{u}} (n : ℕ) (P : ClosedStablePredicate X) :
    ClosedStablePredicate (sStableModel n X) :=
  ClosedStablePredicate.iInter (fun a : (arNerve n) _⦋0⦌ => P.comap (sStableEvaluation n X a))

/-- S_n 上の所属条件は全 Ar 成分での元の条件そのもの。 -/
lemma sClosedPredicate_iff {X : StableModel.{u}} (n : ℕ) (P : ClosedStablePredicate X)
    (v : (sConstruction n X.carrier) _⦋0⦌) :
    (sClosedPredicate n P).predicate v ↔
      ∀ a : (arNerve n) _⦋0⦌,
        P.predicate ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a).app (Opposite.op ⦋0⦌) v.val) := Iff.rfl

end SerrePositivity.KST.SConstruction
