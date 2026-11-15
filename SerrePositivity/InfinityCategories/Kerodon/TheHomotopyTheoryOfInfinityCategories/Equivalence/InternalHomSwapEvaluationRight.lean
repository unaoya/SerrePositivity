module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.InternalHomSwap

/-!
概要：内部Homの交換と第二変数の固定点評価の整合性。
方針：同じ交換同型の逆と、既存の第一変数評価の式を使う。
規約：quasicategoryの仮定は不要。
使われ方：Kerodon §4.5.3（Tag 032Y）の内部Homの交換を使う、指定二変数同型の係数評価。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
namespace Equivalence

/-- 概要：内部Homの交換後の第二変数評価は、同じ評価による内部後合成。
方針：交換の逆で前合成して、既存の第一変数評価の法則へ戻す。
規約：任意の頂点を許す。使われ方：転置同型の指定係数での値の照合。 -/
lemma internalHomSwapIso_evaluate_right (A B X : SSet.{u}) (b : B _⦋0⦌) :
    (internalHomSwapIso A B X).hom ≫ evaluateFunctorAt (Y := (ihom A).obj X) b =
      (ihom A).map (evaluateFunctorAt (Y := X) b) := by
  apply (cancel_epi (internalHomSwapIso A B X).inv).mp
  rw [Iso.inv_hom_id_assoc]
  change evaluateFunctorAt (Y := (ihom A).obj X) b =
    (internalHomSwapIso B A X).hom ≫ (ihom A).map (evaluateFunctorAt (Y := X) b)
  exact (internalHomSwapIso_evaluate B A X b).symm

end Equivalence
end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
