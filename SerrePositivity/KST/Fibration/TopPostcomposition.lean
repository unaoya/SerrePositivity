module
public import SerrePositivity.KST.Fibration.WeakStringConstantPostcomposition
public import SerrePositivity.KST.SConstruction.ClosedSubcategoryFunctor

/-! # 元の完全関手による全頂点部分圏の後合成 -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 有限比較の初期頂点の値域となる、同じ全頂点部分圏の完全関手。 -/
def topPostExact {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) :
    closedStableModel (ClosedStablePredicate.top (sInputModel A)) ⟶
      closedStableModel (ClosedStablePredicate.top (sInputModel B)) :=
  closedStableMap (ClosedStablePredicate.top (sInputModel A))
    (ClosedStablePredicate.top (sInputModel B)) (sInputExactMap f) (fun _ _ => trivial)

/-- 全頂点部分圏への制限は、元の包含と元の完全関手の可換性を保つ。 -/
lemma topPostExact_inclusion {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) :
    topPostExact f ≫ closedStableInclusion (ClosedStablePredicate.top (sInputModel B)) =
      closedStableInclusion (ClosedStablePredicate.top (sInputModel A)) ≫ sInputExactMap f :=
  closedStableMap_inclusion _ _ _ _

end SerrePositivity.KST.Fibration
