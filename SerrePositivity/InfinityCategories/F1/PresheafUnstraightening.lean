module

public import SerrePositivity.InfinityCategories.F1.PresheafInfinity
public import SerrePositivity.InfinityCategories.F1.SmallLeftUnstraighteningBaseChange
public import SerrePositivity.InfinityCategories.F1B.CofinalOppositeFibration

/-!
概要：一般の空間値前層から、同じ小さい底上の実際の right fibration を構成する。
方針：反対の底上の小さい left unstraightening を反転し、二重反転の同型で底を戻す。
規約：対象の構成と底変換を扱い、前層全体の unstraightening ∞ 関手は主張しない。
使われ方：F1-2 の前層と right fibrations の接続、および表現可能前層の全空間。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 小さい底上の前層の right unstraightening の全空間。 -/
def smallRightUnstraightening {C : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) : SSet.{u} :=
  (smallLeftUnstraightening F).op

/-- 前層の right unstraightening は、元の底 C への実際の射影を持つ。 -/
def smallRightUnstraighteningProjection {C : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) :
    smallRightUnstraightening F ⟶ C :=
  SSet.opFunctor.map (smallLeftUnstraighteningProjection F) ≫
    (SSet.opFunctorCompOpFunctorIso.app C).hom

/-- 小さい前層の unstraightening の射影は right fibration。 -/
instance smallRightUnstraighteningProjection_rightFibration {C : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) :
    RightFibration (smallRightUnstraighteningProjection F) where
  mem := rightFibrations.comp_mem _ _
    (RightFibration.mem (p := SSet.opFunctor.map (smallLeftUnstraighteningProjection F)))
    (MorphismProperty.of_isIso rightFibrations (SSet.opFunctorCompOpFunctorIso.app C).hom)

/-- 全空間を反転して戻すと、元の小さい left unstraightening と厳密に同型。 -/
def smallRightUnstraighteningOppositeIso {C : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) :
    (smallRightUnstraightening F).op ≅ smallLeftUnstraightening F :=
  SSet.opFunctorCompOpFunctorIso.app (smallLeftUnstraightening F)

/-- 同じ全空間の同型は、反転した射影と元の left 射影の間で底を保つ。 -/
lemma smallRightUnstraighteningProjection_op {C : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) :
    SSet.opFunctor.map (smallRightUnstraighteningProjection F) =
      (smallRightUnstraighteningOppositeIso F).hom ≫ smallLeftUnstraighteningProjection F := by
  have h := SSet.opFunctorCompOpFunctorIso.hom.naturality
    (smallLeftUnstraighteningProjection F)
  convert h using 1 <;> rfl

/-- 底の可換な射は、前層の小さい right unstraightening 間の実際の射を与える。 -/
def smallRightUnstraighteningMap {C D : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u})
    (G : (SSet.uliftFunctor.{u + 1, u}).obj D.op ⟶ SpaceInfinity.{u})
    (f : C ⟶ D)
    (h : (SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctor.map f) ≫ G = F) :
    smallRightUnstraightening F ⟶ smallRightUnstraightening G :=
  SSet.opFunctor.map (smallLeftUnstraighteningMap F G (SSet.opFunctor.map f) h)

/-- 前層の right unstraightening の比較射は、指定した元の底の射を厳密に被覆する。 -/
lemma smallRightUnstraighteningMap_projection {C D : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u})
    (G : (SSet.uliftFunctor.{u + 1, u}).obj D.op ⟶ SpaceInfinity.{u})
    (f : C ⟶ D)
    (h : (SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctor.map f) ≫ G = F) :
    smallRightUnstraighteningMap F G f h ≫ smallRightUnstraighteningProjection G =
      smallRightUnstraighteningProjection F ≫ f := by
  have hp := smallLeftUnstraighteningMap_projection F G (SSet.opFunctor.map f) h
  have he := congrArg
    (fun k => SSet.opFunctor.map k ≫ (SSet.opFunctorCompOpFunctorIso.app D).hom) hp
  simp only [Functor.map_comp, Category.assoc] at he
  have hn := SSet.opFunctorCompOpFunctorIso.hom.naturality f
  change SSet.opFunctor.map (SSet.opFunctor.map f) ≫
      (SSet.opFunctorCompOpFunctorIso.app D).hom =
    (SSet.opFunctorCompOpFunctorIso.app C).hom ≫ f at hn
  rw [hn] at he
  exact he

end SerrePositivity.InfinityCategories
