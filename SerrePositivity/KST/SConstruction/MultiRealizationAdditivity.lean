module
public import SerrePositivity.KST.SConstruction.IteratedAdditivityRows

/-! # 全有限反復 core S• 実現の加法性
概要：一回以上の全ての反復で、元の subobject・quotient の射対は局所化同型。
方針：行ごとの加法性を対角に移し、入力に自然な既存の反復座標同型で戻す。
規約：零回の core に加法性は主張しない。使われ方：連結 K の加法性と delooping。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.SimplicialModel

/-- 既存の反復座標同型は subobject・quotient の元の射対と可換。 -/
lemma iteratedSRealizationCoordinateIso_additivity (r : ℕ) (X : StableModel.{u}) :
    iteratedSAdditivityMap r X ≫
      ((iteratedSRealizationCoordinateIso r X).hom ⊗ₘ
        (iteratedSRealizationCoordinateIso r X).hom) =
    (iteratedSRealizationCoordinateIso r (cofiberStableModel X)).hom ≫
      multiRealizationAdditivityMap (r + 1) X := by
  rw [iteratedSAdditivityMap_eq]
  change CartesianMonoidalCategory.lift
      (iteratedSRealizationMap r (cofiberStableSubobject X))
      (iteratedSRealizationMap r (cofiberStableQuotient X)) ≫
        ((iteratedSRealizationCoordinateIso r X).hom ⊗ₘ
          (iteratedSRealizationCoordinateIso r X).hom) =
    (iteratedSRealizationCoordinateIso r (cofiberStableModel X)).hom ≫
      CartesianMonoidalCategory.lift
        ((multiRealizationFunctor (r + 1)).map (cofiberStableSubobject X))
        ((multiRealizationFunctor (r + 1)).map (cofiberStableQuotient X))
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, CartesianMonoidalCategory.tensorHom_fst,
      CartesianMonoidalCategory.lift_fst_assoc]
    exact iteratedSRealizationCoordinateIso_naturality r (cofiberStableSubobject X)
  · simp only [Category.assoc, CartesianMonoidalCategory.tensorHom_snd,
      CartesianMonoidalCategory.lift_snd_assoc]
    exact iteratedSRealizationCoordinateIso_naturality r (cofiberStableQuotient X)

/-- 前段の反復加法性から次の回数の元の射対の加法性を得る。 -/
lemma multiRealizationAdditivityMap_step_localized_isIso (r : ℕ)
    (hr : ∀ X : StableModel.{u},
      IsIso (AnodyneHomotopy.anodyneQ.map (multiRealizationAdditivityMap r X)))
    (X : StableModel.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (multiRealizationAdditivityMap (r + 1) X)) := by
  let Q := AnodyneHomotopy.anodyneQ
  have := iteratedSAdditivityMap_localized_isIso r hr X
  have he := congrArg Q.map (iteratedSRealizationCoordinateIso_additivity r X)
  rw [Q.map_comp, Q.map_comp] at he
  have hi : IsIso (Q.map (iteratedSRealizationCoordinateIso r (cofiberStableModel X)).hom ≫
      Q.map (multiRealizationAdditivityMap (r + 1) X)) := he ▸ inferInstance
  exact (isIso_comp_left_iff _ _).mp hi

/-- 全ての正の有限反復における core S• 実現の加法性。 -/
lemma multiRealizationAdditivityMap_localized_isIso (r : ℕ) (X : StableModel.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (multiRealizationAdditivityMap (r + 1) X)) := by
  induction r generalizing X with
  | zero => exact multiRealizationAdditivityMap_one_localized_isIso X
  | succ r ih => exact multiRealizationAdditivityMap_step_localized_isIso (r + 1) ih X

/-- 任意の正の回数として指定した有限反復の加法性。 -/
lemma multiRealizationAdditivityMap_localized_isIso_of_pos (r : ℕ) (hr : 0 < r)
    (X : StableModel.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (multiRealizationAdditivityMap r X)) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  exact multiRealizationAdditivityMap_localized_isIso r X

end SerrePositivity.KST.SConstruction
