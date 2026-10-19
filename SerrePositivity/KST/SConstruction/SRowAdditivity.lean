module
public import SerrePositivity.KST.SConstruction.SCofiberStableIso

/-! # 各 S_n 行での加法性
概要：S_n(cofiber C) の subobject・quotient の射対は、さらに object/core S• 実現の後で弱同値。
方針：S/cofiber の交換同型と S_n C に対する単回加法性を照合する。
規約：n の面・退化との自然性と全多重対角への移行は別に証明する。
使われ方：加法性の有限反復の行ごとの入力。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.SimplicialModel

/-- 任意の関手の下で、S/cofiber の交換は subobject・quotient の射対と可換。 -/
lemma sCofiberStableIso_pair (F : StableModel.{u} ⥤ SSet.{u}) (n : ℕ) (X : StableModel.{u}) :
    F.map (sCofiberStableIso n X).hom ≫ CartesianMonoidalCategory.lift
      (F.map (cofiberStableSubobject (sStableModel n X)))
      (F.map (cofiberStableQuotient (sStableModel n X))) =
    CartesianMonoidalCategory.lift
      (F.map ((sEndofunctor n).map (cofiberStableSubobject X)))
      (F.map ((sEndofunctor n).map (cofiberStableQuotient X))) := by
  rw [CartesianMonoidalCategory.comp_lift, ← F.map_comp, ← F.map_comp,
    sCofiberStableIso_subobject, sCofiberStableIso_quotient]

/-- 各 S_n の後の core S• 実現の加法性の射対。 -/
def coreSRowAdditivityMap (n : ℕ) (X : StableModel.{u}) :
    coreSRealizationFunctor.obj (sStableModel n (cofiberStableModel X)) ⟶
      coreSRealizationFunctor.obj (sStableModel n X) ⊗
        coreSRealizationFunctor.obj (sStableModel n X) :=
  CartesianMonoidalCategory.lift
    (coreSRealizationFunctor.map ((sEndofunctor n).map (cofiberStableSubobject X)))
    (coreSRealizationFunctor.map ((sEndofunctor n).map (cofiberStableQuotient X)))

/-- 任意の S_n 行で subobject・quotient の core 実現は局所化同型。 -/
lemma coreSRowAdditivityMap_localized_isIso (n : ℕ) (X : StableModel.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (coreSRowAdditivityMap n X)) := by
  let Q := AnodyneHomotopy.anodyneQ
  have := coreSAdditivityMap_localized_isIso (sStableModel n X)
  have hi : IsIso (Q.map
      (coreSRealizationFunctor.map (sCofiberStableIso n X).hom ≫
        coreSAdditivityMap (sStableModel n X))) := by
    rw [Q.map_comp]
    infer_instance
  change IsIso (Q.map (coreSRealizationFunctor.map (sCofiberStableIso n X).hom ≫
    CartesianMonoidalCategory.lift
      (coreSRealizationFunctor.map (cofiberStableSubobject (sStableModel n X)))
      (coreSRealizationFunctor.map (cofiberStableQuotient (sStableModel n X))))) at hi
  rw [sCofiberStableIso_pair] at hi
  exact hi

/-- 各 S_n の後の object S• の加法性の射対。 -/
def objectSRowAdditivityMap (n : ℕ) (X : StableModel.{u}) :
    objectSConstructionFunctor.obj (sStableModel n (cofiberStableModel X)) ⟶
      objectSConstructionFunctor.obj (sStableModel n X) ⊗
        objectSConstructionFunctor.obj (sStableModel n X) :=
  CartesianMonoidalCategory.lift
    (objectSConstructionFunctor.map ((sEndofunctor n).map (cofiberStableSubobject X)))
    (objectSConstructionFunctor.map ((sEndofunctor n).map (cofiberStableQuotient X)))

/-- 任意の S_n 行で subobject・quotient の object S• は局所化同型。 -/
lemma objectSRowAdditivityMap_localized_isIso (n : ℕ) (X : StableModel.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (objectSRowAdditivityMap n X)) := by
  let Q := AnodyneHomotopy.anodyneQ
  have := objectSAdditivityMap_localized_isIso (sStableModel n X)
  have hi : IsIso (Q.map
      (objectSConstructionFunctor.map (sCofiberStableIso n X).hom ≫
        objectSAdditivityMap (sStableModel n X))) := by
    rw [Q.map_comp]
    infer_instance
  change IsIso (Q.map (objectSConstructionFunctor.map (sCofiberStableIso n X).hom ≫
    CartesianMonoidalCategory.lift
      (objectSConstructionFunctor.map (cofiberStableSubobject (sStableModel n X)))
      (objectSConstructionFunctor.map (cofiberStableQuotient (sStableModel n X))))) at hi
  rw [sCofiberStableIso_pair] at hi
  exact hi

end SerrePositivity.KST.SConstruction
