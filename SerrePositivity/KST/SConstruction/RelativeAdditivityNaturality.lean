module
public import SerrePositivity.KST.SConstruction.RelativeEvaluationNaturality
public import SerrePositivity.KST.SConstruction.RelativeMultiRealizationAdditivity

/-! # 全正有限反復の相対加法性の自然性
概要：相対 E(A,C,B) の元の射対を、両端を保つ完全関手に関して自然な局所化同型に束ねる。
方針：二評価の完全な自然変換を反復実現で写し、証明済みの正の全反復加法性で同型化する。
規約：成分は元の subobject・quotient の射対。使われ方：連結 K の相対加法性と fibration。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.SimplicialModel

/-- 任意の実現関手の下で、相対二評価の射対は相対入力について自然。 -/
lemma relativeCofiberPair_naturality (F : StableModel.{u} ⥤ SSet.{u})
    {X Y : RelativeStableModel.{u}} (f : X ⟶ Y) :
    F.map (relativeCofiberMap f) ≫ CartesianMonoidalCategory.lift
        (F.map (relativeCofiberSubobject Y.left Y.right))
        (F.map (relativeCofiberQuotient Y.left Y.right)) =
      CartesianMonoidalCategory.lift
        (F.map (relativeCofiberSubobject X.left X.right))
        (F.map (relativeCofiberQuotient X.left X.right)) ≫
          (F.map (relativeLeftFunctor.map f) ⊗ₘ F.map (relativeRightFunctor.map f)) := by
  rw [CartesianMonoidalCategory.comp_lift, CartesianMonoidalCategory.lift_map,
    ← F.map_comp, ← F.map_comp, relativeCofiberSubobject_naturality,
    relativeCofiberQuotient_naturality, F.map_comp, F.map_comp]

/-- 任意の実現関手での相対二評価の射対の自然変換。 -/
def relativeAdditivityNat (F : StableModel.{u} ⥤ SSet.{u}) :
    relativeCofiberFunctor ⋙ F ⟶ (relativeLeftFunctor ⋙ F) ⊗ (relativeRightFunctor ⋙ F) where
  app X := CartesianMonoidalCategory.lift
    (F.map (relativeCofiberSubobject X.left X.right))
    (F.map (relativeCofiberQuotient X.left X.right))
  naturality {_X _Y} f := relativeCofiberPair_naturality F f

/-- 全有限反復の相対加法性の元の射対を自然変換に束ねる。 -/
def relativeMultiRealizationAdditivityNat (r : ℕ) :
    relativeCofiberFunctor.{u} ⋙ multiRealizationFunctor r ⟶
      (relativeLeftFunctor ⋙ multiRealizationFunctor r) ⊗
        (relativeRightFunctor ⋙ multiRealizationFunctor r) :=
  relativeAdditivityNat (multiRealizationFunctor r)

/-- 全ての正の有限反復の相対加法性は局所化後に自然同型。 -/
def relativeMultiRealizationAdditivityLocalizedIso (r : ℕ) :
    relativeCofiberFunctor.{u} ⋙ multiRealizationFunctor (r + 1) ⋙ AnodyneHomotopy.anodyneQ ≅
      ((relativeLeftFunctor ⋙ multiRealizationFunctor (r + 1)) ⊗
        (relativeRightFunctor ⋙ multiRealizationFunctor (r + 1))) ⋙ AnodyneHomotopy.anodyneQ := by
  let η := Functor.whiskerRight (relativeMultiRealizationAdditivityNat (r + 1))
    AnodyneHomotopy.anodyneQ
  have (X : RelativeStableModel.{u}) : IsIso (η.app X) :=
    relativeMultiRealizationAdditivityMap_localized_isIso r X.left X.right
  have : IsIso η := NatIso.isIso_of_isIso_app _
  exact asIso η

/-- 自然同型の成分は元の相対加法性の射対の像に一致する。 -/
lemma relativeMultiRealizationAdditivityLocalizedIso_app (r : ℕ) (X : RelativeStableModel.{u}) :
    (relativeMultiRealizationAdditivityLocalizedIso r).hom.app X =
      AnodyneHomotopy.anodyneQ.map (relativeMultiRealizationAdditivityMap (r + 1) X.left X.right) :=
  rfl

end SerrePositivity.KST.SConstruction
