module
public import SerrePositivity.KST.SConstruction.SRelativeCofiberIso

/-! # 相対 S/cofiber 交換と二つの評価
概要：相対交換同型が subobject・quotient の元の完全関手を保つことを照合する。
方針：閉じた全部分圏の包含で検査し、全 cofiber の交換式に帰着する。
規約：両端の S_n A/B との比較を明示する。使われ方：相対行の加法性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 相対交換は subobject の完全関手と端の部分圏比較に関して厳密に可換。 -/
lemma sRelativeCofiberStableIso_subobject {X : StableModel.{u}} (n : ℕ)
    (A B : ClosedStablePredicate X) :
    (sRelativeCofiberStableIso n A B).hom ≫
        relativeCofiberSubobject (sClosedPredicate n A) (sClosedPredicate n B) =
      (sEndofunctor n).map (relativeCofiberSubobject A B) ≫ (sClosedStableIso n A).hom := by
  apply closedStableInclusion_cancel (sClosedPredicate n A)
  calc
    _ = (sRelativeCofiberStableIso n A B).hom ≫
        (relativeCofiberInclusion (sClosedPredicate n A) (sClosedPredicate n B) ≫
          cofiberStableSubobject (sStableModel n X)) :=
      (Category.assoc _ _ _).trans (congrArg
        (fun f => (sRelativeCofiberStableIso n A B).hom ≫ f)
        (relativeCofiberSubobject_inclusion (sClosedPredicate n A) (sClosedPredicate n B)))
    _ = ((sEndofunctor n).map (relativeCofiberInclusion A B) ≫
        (sCofiberStableIso n X).hom) ≫ cofiberStableSubobject (sStableModel n X) :=
      (Category.assoc _ _ _).symm.trans (congrArg
        (fun f => f ≫ cofiberStableSubobject (sStableModel n X))
        (sRelativeCofiberStableIso_inclusion n A B))
    _ = (sEndofunctor n).map (relativeCofiberInclusion A B) ≫
        (sEndofunctor n).map (cofiberStableSubobject X) :=
      (Category.assoc _ _ _).trans (congrArg
        (fun f => (sEndofunctor n).map (relativeCofiberInclusion A B) ≫ f)
        (sCofiberStableIso_subobject n X))
    _ = (sEndofunctor n).map (relativeCofiberSubobject A B) ≫
        (sEndofunctor n).map (closedStableInclusion A) := by
      rw [← CategoryTheory.Functor.map_comp, ← relativeCofiberSubobject_inclusion,
        CategoryTheory.Functor.map_comp]
    _ = _ := (congrArg (fun f => (sEndofunctor n).map (relativeCofiberSubobject A B) ≫ f)
      (sClosedStableIso_inclusion n A).symm).trans (Category.assoc _ _ _).symm

/-- 相対交換は quotient の完全関手と端の部分圏比較に関して厳密に可換。 -/
lemma sRelativeCofiberStableIso_quotient {X : StableModel.{u}} (n : ℕ)
    (A B : ClosedStablePredicate X) :
    (sRelativeCofiberStableIso n A B).hom ≫
        relativeCofiberQuotient (sClosedPredicate n A) (sClosedPredicate n B) =
      (sEndofunctor n).map (relativeCofiberQuotient A B) ≫ (sClosedStableIso n B).hom := by
  apply closedStableInclusion_cancel (sClosedPredicate n B)
  calc
    _ = (sRelativeCofiberStableIso n A B).hom ≫
        (relativeCofiberInclusion (sClosedPredicate n A) (sClosedPredicate n B) ≫
          cofiberStableQuotient (sStableModel n X)) :=
      (Category.assoc _ _ _).trans (congrArg
        (fun f => (sRelativeCofiberStableIso n A B).hom ≫ f)
        (relativeCofiberQuotient_inclusion (sClosedPredicate n A) (sClosedPredicate n B)))
    _ = ((sEndofunctor n).map (relativeCofiberInclusion A B) ≫
        (sCofiberStableIso n X).hom) ≫ cofiberStableQuotient (sStableModel n X) :=
      (Category.assoc _ _ _).symm.trans (congrArg
        (fun f => f ≫ cofiberStableQuotient (sStableModel n X))
        (sRelativeCofiberStableIso_inclusion n A B))
    _ = (sEndofunctor n).map (relativeCofiberInclusion A B) ≫
        (sEndofunctor n).map (cofiberStableQuotient X) :=
      (Category.assoc _ _ _).trans (congrArg
        (fun f => (sEndofunctor n).map (relativeCofiberInclusion A B) ≫ f)
        (sCofiberStableIso_quotient n X))
    _ = (sEndofunctor n).map (relativeCofiberQuotient A B) ≫
        (sEndofunctor n).map (closedStableInclusion B) := by
      rw [← CategoryTheory.Functor.map_comp, ← relativeCofiberQuotient_inclusion,
        CategoryTheory.Functor.map_comp]
    _ = _ := (congrArg (fun f => (sEndofunctor n).map (relativeCofiberQuotient A B) ≫ f)
      (sClosedStableIso_inclusion n B).symm).trans (Category.assoc _ _ _).symm

end SerrePositivity.KST.SConstruction
