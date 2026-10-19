module
public import SerrePositivity.KST.SConstruction.CofiberEndofunctor
public import SerrePositivity.KST.SConstruction.MultiRealizationAdditivity

/-! # 全有限反復の加法性の自然性
概要：元の subobject・quotient の射対は、安定な入力の完全関手に関して自然。
方針：cofiber 自己関手の各角の自然性を反復実現で写し、正の段で自然同型へ局所化する。
規約：成分は既に証明した元の加法性の射。使われ方：連結 K 関手の加法性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.SimplicialModel

/-- 任意の実現関手の下で subobject・quotient の射対は入力に関して自然。 -/
lemma cofiberPair_naturality (F : StableModel.{u} ⥤ SSet.{u})
    {X Y : StableModel.{u}} (f : X ⟶ Y) :
    F.map (cofiberEndofunctor.map f) ≫ CartesianMonoidalCategory.lift
      (F.map (cofiberStableSubobject Y)) (F.map (cofiberStableQuotient Y)) =
    CartesianMonoidalCategory.lift
      (F.map (cofiberStableSubobject X)) (F.map (cofiberStableQuotient X)) ≫
        (F.map f ⊗ₘ F.map f) := by
  have hs : F.map (cofiberEndofunctor.map f) ≫ F.map (cofiberStableSubobject Y) =
      F.map (cofiberStableSubobject X) ≫ F.map f := by
    rw [← F.map_comp, ← F.map_comp]
    exact congrArg F.map (cofiberSubobjectNat.naturality f)
  have hq : F.map (cofiberEndofunctor.map f) ≫ F.map (cofiberStableQuotient Y) =
      F.map (cofiberStableQuotient X) ≫ F.map f := by
    rw [← F.map_comp, ← F.map_comp]
    exact congrArg F.map (cofiberQuotientNat.naturality f)
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, CartesianMonoidalCategory.tensorHom_fst,
      CartesianMonoidalCategory.lift_fst_assoc, CartesianMonoidalCategory.lift_fst]
    exact hs
  · simp only [Category.assoc, CartesianMonoidalCategory.tensorHom_snd,
      CartesianMonoidalCategory.lift_snd_assoc, CartesianMonoidalCategory.lift_snd]
    exact hq

/-- 全ての有限反復の元の加法性の射対を自然変換に束ねる。 -/
def multiRealizationAdditivityNat (r : ℕ) :
    cofiberEndofunctor.{u} ⋙ multiRealizationFunctor r ⟶
      multiRealizationFunctor r ⊗ multiRealizationFunctor r where
  app X := multiRealizationAdditivityMap r X
  naturality {_X _Y} f := cofiberPair_naturality (multiRealizationFunctor r) f

/-- 正の有限反復の加法性の射対は局所化後に自然同型を与える。 -/
def multiRealizationAdditivityLocalizedIso (r : ℕ) :
    cofiberEndofunctor.{u} ⋙ multiRealizationFunctor (r + 1) ⋙ AnodyneHomotopy.anodyneQ ≅
      (multiRealizationFunctor (r + 1) ⊗ multiRealizationFunctor (r + 1)) ⋙
        AnodyneHomotopy.anodyneQ := by
  let η := Functor.whiskerRight (multiRealizationAdditivityNat (r + 1)) AnodyneHomotopy.anodyneQ
  have (X : StableModel.{u}) : IsIso (η.app X) := multiRealizationAdditivityMap_localized_isIso r X
  have : IsIso η := NatIso.isIso_of_isIso_app _
  exact asIso η

/-- 局所化した自然同型の成分は元の加法性の射対の像。 -/
lemma multiRealizationAdditivityLocalizedIso_app (r : ℕ) (X : StableModel.{u}) :
    (multiRealizationAdditivityLocalizedIso r).hom.app X =
      AnodyneHomotopy.anodyneQ.map (multiRealizationAdditivityMap (r + 1) X) := rfl

end SerrePositivity.KST.SConstruction
