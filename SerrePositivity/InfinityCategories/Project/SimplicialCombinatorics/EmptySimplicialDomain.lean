module

public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
概要：空の単体的定義域と、その任意の引き戻しの始対象性。
方針：次数ごとの空性から唯一の射を構成し、始対象から空部分複体への射で逆を示す。
規約：底と射影の充填性は不要。
使われ方：空の境界上の元の Hom の終対象性。
-/

@[expose] public section
noncomputable section
universe u v
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-- 各次数が空なら、同じ単体集合は始対象。 -/
def sset_isInitial_of_obj_isEmpty (A : SSet.{u}) [∀ n, IsEmpty (A.obj n)] : IsInitial A := by
  refine IsInitial.ofUniqueHom (fun X ↦
    { app := fun _ ↦ ↾fun x ↦ isEmptyElim x
      naturality := by intro n m f; ext x; exact isEmptyElim x }) ?_
  intro X f
  apply SSet.hom_ext
  intro n
  ext x
  exact isEmptyElim x

/-- 始対象の各次数は、空部分複体への唯一の射により空。 -/
lemma sset_obj_isEmpty_of_isInitial {A : SSet.{u}} (hA : IsInitial A) (n : SimplexCategoryᵒᵖ) :
    IsEmpty (A.obj n) :=
  ⟨fun x ↦ ((hA.to (⊥ : A.Subcomplex)).app n x).property⟩

/-- 空の底からの任意の引き戻しも、実際に始対象。 -/
def sset_pullback_isInitial_of_left {A E B : SSet.{u}}
    (a : A ⟶ B) (p : E ⟶ B) (hA : IsInitial A) : IsInitial (pullback a p) := by
  letI (n : SimplexCategoryᵒᵖ) : IsEmpty (A.obj n) := sset_obj_isEmpty_of_isInitial hA n
  letI (n : SimplexCategoryᵒᵖ) : IsEmpty ((pullback a p).obj n) :=
    Function.isEmpty ((pullback.fst a p).app n)
  exact sset_isInitial_of_obj_isEmpty _

/-- 空の単体集合を宇宙持ち上げしても、同じ次数ごとの空性により始対象。 -/
def uliftSSet_isInitial_of_isInitial {A : SSet.{u}} (hA : IsInitial A) :
    IsInitial ((SSet.uliftFunctor.{v, u}).obj A) := by
  letI (n : SimplexCategoryᵒᵖ) : IsEmpty (A.obj n) := sset_obj_isEmpty_of_isInitial hA n
  letI (n : SimplexCategoryᵒᵖ) : IsEmpty (((SSet.uliftFunctor.{v, u}).obj A).obj n) :=
    Function.isEmpty (ULift.down : ULift.{v, u} (A.obj n) → A.obj n)
  exact sset_isInitial_of_obj_isEmpty _

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
