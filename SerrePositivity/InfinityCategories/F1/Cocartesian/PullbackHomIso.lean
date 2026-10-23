module

public import SerrePositivity.InfinityCategories.F1.RelativeFunctorIsPullbackIso
public import SerrePositivity.InfinityCategories.F1.Cocartesian.PullbackHomRestriction
public import SerrePositivity.InfinityCategories.Core.FullSubcomplexIso

/-!
概要：両射影の底変換間の元の cocartesian Hom と、元の標的へ写す局所 Hom は厳密に同型。
方針：全相対関手空間の pullback 同型を、標的の辺の保存・反映で全部分複体へ制限する。
規約：可変の底には quasicategory 性を要求せず、全高次の元の相対作用を保持する。
使われ方：底の余極限の Hom の降下を、実際の各底変換の cocartesian Hom に接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 各底変換の元の全相対 Hom を、元の標的へ写す同じ全相対 Hom と同型化する。 -/
def cocartesianPullbackRawHomIso {E F B : SSet.{u}} (p : E ⟶ B) (q : F ⟶ B) (a : Over B) :
    relativeFunctorSpace (pullback.fst a.hom q) (pullback.fst a.hom p) ≅
      relativeFunctorSpace q (pullback.snd a.hom p ≫ p) :=
  relativeFunctorIsPullbackIso (IsPullback.of_hasPullback a.hom q).flip
    (pullback.fst a.hom p) (pullback.snd a.hom p ≫ p) (by exact pullback.condition)

/-- 同じ全相対 Hom の同型は、元の各底変換の cocartesian 辺の保存条件を反映する。 -/
lemma cocartesianPullbackRawHomIso_predicate {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [CocartesianFibration q] (a : Over B)
    (v : (relativeFunctorSpace (pullback.fst a.hom q) (pullback.fst a.hom p)) _⦋0⦌) :
    cocartesianRelativeFunctorPredicate (pullback.fst a.hom p) (pullback.fst a.hom q) v ↔
      markedCocartesianFunctorPredicate q (pullback.snd a.hom p ≫ p)
        {e | IsCocartesianEdge (pullback.fst a.hom p) e}
        ((cocartesianPullbackRawHomIso p q a).hom.app (Opposite.op ⦋0⦌) v) := by
  obtain ⟨g, hg, rfl⟩ := exists_relativeFunctorVertex (pullback.fst a.hom q)
    (pullback.fst a.hom p) v
  rw [cocartesianRelativeFunctorPredicate_vertex]
  change PreservesCocartesianEdges (pullback.fst a.hom p) (pullback.fst a.hom q) g ↔
    markedCocartesianFunctorPredicate q _ _
      ((relativeFunctorIsPullbackIso (IsPullback.of_hasPullback a.hom q).flip
        (pullback.fst a.hom p) (pullback.snd a.hom p ≫ p) (by exact pullback.condition)).hom.app _
          (relativeFunctorVertex _ _ g hg))
  rw [relativeFunctorIsPullbackIso_vertex, markedCocartesianFunctorPredicate_vertex]
  exact forall_congr' (fun e ↦ imp_congr_right (fun _ ↦
    isCocartesianEdge_overPullback_iff q a (g.app (Opposite.op ⦋1⦌) e)))

/-- 元の各底変換の全 cocartesian Hom は、同じ局所 Hom と厳密に同型。 -/
def cocartesianPullbackHomIso {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [CocartesianFibration q] (a : Over B) :
    cocartesianRelativeFunctorSpace (pullback.fst a.hom p) (pullback.fst a.hom q) ≅
      cocartesianPullbackHomSpace p q a :=
  fullSubcomplexIso (cocartesianPullbackRawHomIso p q a)
    (cocartesianRelativeFunctorPredicate (pullback.fst a.hom p) (pullback.fst a.hom q))
    (markedCocartesianFunctorPredicate q (pullback.snd a.hom p ≫ p)
      {e | IsCocartesianEdge (pullback.fst a.hom p) e})
    (cocartesianPullbackRawHomIso_predicate p q a)

end SerrePositivity.InfinityCategories
