module
public import SerrePositivity.KST.SConstruction.SRowAdditivity

/-! # 一回の反復実現の加法性
概要：単回 core S• 実現と既存の多重実現の一回の場合を同定する。
方針：全次数で元の S_n の core を使い、元の完全関手の射を照合する。
規約：零回の core の加法性を主張しない。使われ方：全有限反復の帰納の基底。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.SimplicialModel

/-- 単回 core S• の実現と多重実現の一回の場合の座標同型。 -/
def coreSingleRealizationIso (X : StableModel.{u}) :
    coreSRealizationFunctor.obj X ≅ (multiRealizationFunctor 1).obj X :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

/-- 単回の座標同型は安定な入力の完全関手に関して自然。 -/
lemma coreSingleRealizationIso_naturality {X Y : StableModel.{u}} (f : X ⟶ Y) :
    coreSRealizationFunctor.map f ≫ (coreSingleRealizationIso Y).hom =
      (coreSingleRealizationIso X).hom ≫ (multiRealizationFunctor 1).map f := by
  rfl

/-- 任意の回数の多重実現における元の subobject・quotient の射対。 -/
def multiRealizationAdditivityMap (r : ℕ) (X : StableModel.{u}) :
    (multiRealizationFunctor r).obj (cofiberStableModel X) ⟶
      (multiRealizationFunctor r).obj X ⊗ (multiRealizationFunctor r).obj X :=
  CartesianMonoidalCategory.lift
    ((multiRealizationFunctor r).map (cofiberStableSubobject X))
    ((multiRealizationFunctor r).map (cofiberStableQuotient X))

/-- 単回の加法性の比較は多重実現の一回の射対と可換。 -/
lemma coreSingleRealizationIso_additivity (X : StableModel.{u}) :
    coreSAdditivityMap X ≫
      ((coreSingleRealizationIso X).hom ⊗ₘ (coreSingleRealizationIso X).hom) =
    (coreSingleRealizationIso (cofiberStableModel X)).hom ≫ multiRealizationAdditivityMap 1 X := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, CartesianMonoidalCategory.tensorHom_fst]
    change CartesianMonoidalCategory.lift _ _ ≫
      (CartesianMonoidalCategory.fst _ _ ≫ (coreSingleRealizationIso X).hom) =
      (coreSingleRealizationIso (cofiberStableModel X)).hom ≫
        (CartesianMonoidalCategory.lift _ _ ≫ CartesianMonoidalCategory.fst _ _)
    rw [CartesianMonoidalCategory.lift_fst_assoc, CartesianMonoidalCategory.lift_fst]
    exact coreSingleRealizationIso_naturality (cofiberStableSubobject X)
  · simp only [Category.assoc, CartesianMonoidalCategory.tensorHom_snd]
    change CartesianMonoidalCategory.lift _ _ ≫
      (CartesianMonoidalCategory.snd _ _ ≫ (coreSingleRealizationIso X).hom) =
      (coreSingleRealizationIso (cofiberStableModel X)).hom ≫
        (CartesianMonoidalCategory.lift _ _ ≫ CartesianMonoidalCategory.snd _ _)
    rw [CartesianMonoidalCategory.lift_snd_assoc, CartesianMonoidalCategory.lift_snd]
    exact coreSingleRealizationIso_naturality (cofiberStableQuotient X)

/-- 一回の多重実現の元の射対についての加法性。 -/
lemma multiRealizationAdditivityMap_one_localized_isIso (X : StableModel.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (multiRealizationAdditivityMap 1 X)) := by
  let Q := AnodyneHomotopy.anodyneQ
  have := coreSAdditivityMap_localized_isIso X
  have he := congrArg Q.map (coreSingleRealizationIso_additivity X)
  rw [Q.map_comp, Q.map_comp] at he
  have hi : IsIso (Q.map (coreSingleRealizationIso (cofiberStableModel X)).hom ≫
      Q.map (multiRealizationAdditivityMap 1 X)) := he ▸ inferInstance
  exact (isIso_comp_left_iff _ _).mp hi

end SerrePositivity.KST.SConstruction
