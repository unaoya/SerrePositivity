module
public import SerrePositivity.KST.SConstruction.SRelativeEvaluation
public import SerrePositivity.KST.SConstruction.RelativeAdditivity

/-! # 各 S_n 行の相対加法性
概要：S_n E(A,C,B) の元の二評価は object/core S• 実現後に積への弱同値。
方針：相対交換同型と両端の全部分圏比較で単回加法性を輸送する。
規約：元の S_n A/B を標的に使う。使われ方：正の有限反復の相対加法性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.SimplicialModel

/-- 相対交換は任意の関手の下で元の二評価の射対と可換。 -/
lemma sRelativeCofiberStableIso_pair (F : StableModel.{u} ⥤ SSet.{u})
    {X : StableModel.{u}} (n : ℕ) (A B : ClosedStablePredicate X) :
    F.map (sRelativeCofiberStableIso n A B).hom ≫ CartesianMonoidalCategory.lift
        (F.map (relativeCofiberSubobject (sClosedPredicate n A) (sClosedPredicate n B)))
        (F.map (relativeCofiberQuotient (sClosedPredicate n A) (sClosedPredicate n B))) =
      CartesianMonoidalCategory.lift
        (F.map ((sEndofunctor n).map (relativeCofiberSubobject A B)))
        (F.map ((sEndofunctor n).map (relativeCofiberQuotient A B))) ≫
          (F.map (sClosedStableIso n A).hom ⊗ₘ F.map (sClosedStableIso n B).hom) := by
  rw [CartesianMonoidalCategory.comp_lift, CartesianMonoidalCategory.lift_map,
    ← F.map_comp, ← F.map_comp, sRelativeCofiberStableIso_subobject,
    sRelativeCofiberStableIso_quotient, F.map_comp, F.map_comp]

/-- 相対行の加法性を、同型による輸送で元の射対へ戻す一般補題。 -/
lemma relativeRowAdditivity_localized_isIso (F : StableModel.{u} ⥤ SSet.{u})
    {X : StableModel.{u}} (n : ℕ) (A B : ClosedStablePredicate X)
    (h : IsIso (AnodyneHomotopy.anodyneQ.map (CartesianMonoidalCategory.lift
      (F.map (relativeCofiberSubobject (sClosedPredicate n A) (sClosedPredicate n B)))
      (F.map (relativeCofiberQuotient (sClosedPredicate n A) (sClosedPredicate n B)))))) :
    IsIso (AnodyneHomotopy.anodyneQ.map (CartesianMonoidalCategory.lift
      (F.map ((sEndofunctor n).map (relativeCofiberSubobject A B)))
      (F.map ((sEndofunctor n).map (relativeCofiberQuotient A B))))) := by
  let Q := AnodyneHomotopy.anodyneQ
  have hi : IsIso (Q.map (F.map (sRelativeCofiberStableIso n A B).hom ≫
      CartesianMonoidalCategory.lift
        (F.map (relativeCofiberSubobject (sClosedPredicate n A) (sClosedPredicate n B)))
        (F.map (relativeCofiberQuotient (sClosedPredicate n A) (sClosedPredicate n B))))) := by
    rw [Q.map_comp]
    infer_instance
  rw [sRelativeCofiberStableIso_pair, Q.map_comp] at hi
  exact (isIso_comp_right_iff _ _).mp hi

/-- S_n E(A,C,B) の元の二評価による core S• 実現の射対。 -/
def relativeCoreSRowAdditivityMap {X : StableModel.{u}} (n : ℕ)
    (A B : ClosedStablePredicate X) :
    coreSRealizationFunctor.obj (sStableModel n (relativeCofiberStableModel A B)) ⟶
      coreSRealizationFunctor.obj (sStableModel n (closedStableModel A)) ⊗
        coreSRealizationFunctor.obj (sStableModel n (closedStableModel B)) :=
  CartesianMonoidalCategory.lift
    (coreSRealizationFunctor.map ((sEndofunctor n).map (relativeCofiberSubobject A B)))
    (coreSRealizationFunctor.map ((sEndofunctor n).map (relativeCofiberQuotient A B)))

/-- 各 S_n 行の相対 core S• 実現の加法性。 -/
lemma relativeCoreSRowAdditivityMap_localized_isIso {X : StableModel.{u}} (n : ℕ)
    (A B : ClosedStablePredicate X) :
    IsIso (AnodyneHomotopy.anodyneQ.map (relativeCoreSRowAdditivityMap n A B)) :=
  relativeRowAdditivity_localized_isIso coreSRealizationFunctor n A B
    (relativeCoreSAdditivityMap_localized_isIso (sClosedPredicate n A) (sClosedPredicate n B))

/-- S_n E(A,C,B) の元の二評価による object S• の射対。 -/
def relativeObjectSRowAdditivityMap {X : StableModel.{u}} (n : ℕ)
    (A B : ClosedStablePredicate X) :
    objectSConstructionFunctor.obj (sStableModel n (relativeCofiberStableModel A B)) ⟶
      objectSConstructionFunctor.obj (sStableModel n (closedStableModel A)) ⊗
        objectSConstructionFunctor.obj (sStableModel n (closedStableModel B)) :=
  CartesianMonoidalCategory.lift
    (objectSConstructionFunctor.map ((sEndofunctor n).map (relativeCofiberSubobject A B)))
    (objectSConstructionFunctor.map ((sEndofunctor n).map (relativeCofiberQuotient A B)))

/-- 各 S_n 行の相対 object S• の加法性。 -/
lemma relativeObjectSRowAdditivityMap_localized_isIso {X : StableModel.{u}} (n : ℕ)
    (A B : ClosedStablePredicate X) :
    IsIso (AnodyneHomotopy.anodyneQ.map (relativeObjectSRowAdditivityMap n A B)) :=
  relativeRowAdditivity_localized_isIso objectSConstructionFunctor n A B
    (relativeObjectSAdditivityMap_localized_isIso (sClosedPredicate n A) (sClosedPredicate n B))

end SerrePositivity.KST.SConstruction
