module
public import SerrePositivity.KST.SConstruction.SRelativeRowAdditivity
public import SerrePositivity.KST.SConstruction.SingleRealizationAdditivity

/-! # 相対加法性の反復の基底
概要：相対図式の元の二評価を任意の有限反復実現で定義し、一回の場合の加法性を示す。
方針：既存の単回 core S• と反復座標の自然な同型で元の射対を照合する。
規約：零回には加法性を主張しない。使われ方：全正反復への帰納。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.SimplicialModel

/-- 相対図式の元の二評価の有限反復実現の射対。 -/
def relativeMultiRealizationAdditivityMap {X : StableModel.{u}} (r : ℕ)
    (A B : ClosedStablePredicate X) :
    (multiRealizationFunctor r).obj (relativeCofiberStableModel A B) ⟶
      (multiRealizationFunctor r).obj (closedStableModel A) ⊗
        (multiRealizationFunctor r).obj (closedStableModel B) :=
  CartesianMonoidalCategory.lift
    ((multiRealizationFunctor r).map (relativeCofiberSubobject A B))
    ((multiRealizationFunctor r).map (relativeCofiberQuotient A B))

/-- 単回の座標比較は相対図式の元の射対を保つ。 -/
lemma coreSingleRealizationIso_relativeAdditivity {X : StableModel.{u}}
    (A B : ClosedStablePredicate X) :
    relativeCoreSAdditivityMap A B ≫
      ((coreSingleRealizationIso (closedStableModel A)).hom ⊗ₘ
        (coreSingleRealizationIso (closedStableModel B)).hom) =
      (coreSingleRealizationIso (relativeCofiberStableModel A B)).hom ≫
        relativeMultiRealizationAdditivityMap 1 A B := by
  change CartesianMonoidalCategory.lift _ _ ≫ (_ ⊗ₘ _) =
    _ ≫ CartesianMonoidalCategory.lift _ _
  rw [CartesianMonoidalCategory.lift_map, CartesianMonoidalCategory.comp_lift,
    coreSingleRealizationIso_naturality, coreSingleRealizationIso_naturality]

/-- 一回の反復実現の相対加法性。 -/
lemma relativeMultiRealizationAdditivityMap_one_localized_isIso {X : StableModel.{u}}
    (A B : ClosedStablePredicate X) :
    IsIso (AnodyneHomotopy.anodyneQ.map (relativeMultiRealizationAdditivityMap 1 A B)) := by
  let Q := AnodyneHomotopy.anodyneQ
  have := relativeCoreSAdditivityMap_localized_isIso A B
  have he := congrArg Q.map (coreSingleRealizationIso_relativeAdditivity A B)
  rw [Q.map_comp, Q.map_comp] at he
  have hi : IsIso (Q.map (coreSingleRealizationIso (relativeCofiberStableModel A B)).hom ≫
      Q.map (relativeMultiRealizationAdditivityMap 1 A B)) := he ▸ inferInstance
  exact (isIso_comp_left_iff _ _).mp hi

end SerrePositivity.KST.SConstruction
