module

public import SerrePositivity.InfinityCategories.F1.EmptySimplicialDomain
public import SerrePositivity.InfinityCategories.F1.MarkedCocartesianFunctorPrecomposition
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
概要：空の定義域上の全相対 Hom と指定辺保存 Hom は、実際の終対象。
方針：空の直積上の一意な射を相対 curry し、展開の単射性で一意性を示す。
規約：標的の fibration 性や底の充填性を仮定しない。
使われ方：標準境界による分類 Hom 比較の初期値。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 空の定義域の元の全相対 Hom は、パラメーターごとの一意な族を持つ終対象。 -/
def relativeFunctorSpace_isTerminal_of_isInitial {A E B : SSet.{u}}
    (q : E ⟶ B) (a : A ⟶ B) (hA : IsInitial A) : IsTerminal (relativeFunctorSpace q a) := by
  refine IsTerminal.ofUniqueHom (fun T ↦ relativeFunctorCurry
    ((hA.isInitialObj (tensorRight T)).to E)
    ((hA.isInitialObj (tensorRight T)).hom_ext _ _)) ?_
  intro T f
  apply relativeFunctorUncurry_injective q a
  exact (hA.isInitialObj (tensorRight T)).hom_ext _ _

/-- 空の定義域には指定辺がないため、同じ辺保存 Hom も終対象。 -/
def markedCocartesianFunctorSpace_isTerminal_of_isInitial {A E B : SSet.{u}}
    (q : E ⟶ B) (a : A ⟶ B) (W : Set (A _⦋1⦌)) (hA : IsInitial A) :
    IsTerminal (markedCocartesianFunctorSpace q a W) := by
  letI : IsEmpty (A _⦋1⦌) := sset_obj_isEmpty_of_isInitial hA _
  refine IsTerminal.ofUniqueHom (fun T ↦ fullSubcomplexLift _
    ((relativeFunctorSpace_isTerminal_of_isInitial q a hA).from T) (by
      intro v e he
      exact isEmptyElim e)) ?_
  intro T f
  apply (cancel_mono (fullSubcomplexOnVertices _ (markedCocartesianFunctorPredicate q a W)).ι).mp
  exact (relativeFunctorSpace_isTerminal_of_isInitial q a hA).hom_ext _ _

end SerrePositivity.InfinityCategories
