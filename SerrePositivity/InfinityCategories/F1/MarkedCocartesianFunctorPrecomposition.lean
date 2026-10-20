module

public import SerrePositivity.InfinityCategories.F1.MarkedCocartesianFunctorSpace

/-!
概要：指定辺を保つ相対関手の空間を、指定辺を保つ始域の射で制限する。
方針：元の相対前合成を全部分複体へ持ち上げる。
規約：始域の射や標的の射影の充填性は不要。
使われ方：元の cocartesian Hom のセルごとの制限と貼り合わせ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 指定辺を保つ相対関手から、元の全相対関手空間への包含。 -/
def markedCocartesianFunctorInclusion {A E B : SSet.{u}} (q : E ⟶ B) (a : A ⟶ B)
    (W : Set (A _⦋1⦌)) : markedCocartesianFunctorSpace q a W ⟶ relativeFunctorSpace q a :=
  (fullSubcomplexOnVertices _ (markedCocartesianFunctorPredicate q a W)).ι

/-- 指定辺を保つ始域の射による、元の相対 Hom の制限。 -/
def markedCocartesianFunctorPre {E B : SSet.{u}} (q : E ⟶ B) {a b : Over B}
    (i : a ⟶ b) (V : Set (a.left _⦋1⦌)) (W : Set (b.left _⦋1⦌))
    (hi : ∀ e ∈ V, i.left.app (Opposite.op ⦋1⦌) e ∈ W) :
    markedCocartesianFunctorSpace q b.hom W ⟶ markedCocartesianFunctorSpace q a.hom V :=
  fullSubcomplexLift _ (markedCocartesianFunctorInclusion q b.hom W ≫
    relativeFunctorOverPre q i) (by
      intro v
      obtain ⟨f, hf, hv⟩ := exists_relativeFunctorVertex q b.hom v.val
      have h := fullSubcomplexOnVertices_vertex v
      change markedCocartesianFunctorPredicate q b.hom W v.val at h
      rw [← hv, markedCocartesianFunctorPredicate_vertex] at h
      change markedCocartesianFunctorPredicate q a.hom V
        ((relativeFunctorOverPre q i).app (Opposite.op ⦋0⦌) v.val)
      rw [← hv, relativeFunctorOverPre_vertex, markedCocartesianFunctorPredicate_vertex]
      intro e he
      exact h _ (hi e he))

/-- 指定辺を保つ制限は、包含後に元の全相対前合成そのものとなる。 -/
lemma markedCocartesianFunctorPre_ι {E B : SSet.{u}} (q : E ⟶ B) {a b : Over B}
    (i : a ⟶ b) (V : Set (a.left _⦋1⦌)) (W : Set (b.left _⦋1⦌))
    (hi : ∀ e ∈ V, i.left.app (Opposite.op ⦋1⦌) e ∈ W) :
    markedCocartesianFunctorPre q i V W hi ≫ markedCocartesianFunctorInclusion q a.hom V =
      markedCocartesianFunctorInclusion q b.hom W ≫ relativeFunctorOverPre q i :=
  fullSubcomplexLift_ι _ _ _

end SerrePositivity.InfinityCategories
