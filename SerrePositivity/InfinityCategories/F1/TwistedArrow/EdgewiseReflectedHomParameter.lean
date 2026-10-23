module

public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftPointHomReverseComposition
public import SerrePositivity.InfinityCategories.F1.TwistedArrow.EdgewiseOppositeKanEnriched

/-!
概要：Hom の共通解像の反転した左端射影と、直接の Kan 作用のパラメーターの照合。
方針：左端射影を反転して二重反転を戻し、同じ反転した内部 Hom へ送る。
規約：共通解像自身の反転を保持し、右端射影との同一視は行わない。
使われ方：pointed 輸送の直接の作用を全対象の共同反転比較と同じ族に接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 任意の共通解像の左端を反転し、元のパラメーターへ戻す射。 -/
def edgewiseReflectedParameter (H : SSet.{u}) :
    ((SSet.uliftFunctor.{u + 1, u}).obj (edgewiseSubdivision H)).op ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj H :=
  (HomotopyLimits.uliftOppositeIso (edgewiseSubdivision H)).inv ≫
    (SSet.uliftFunctor.{u + 1, u}).map
      (SSet.opFunctor.map (edgewiseLeft H) ≫ (SSet.opFunctorCompOpFunctorIso.app H).hom)

/-- 同じ反転した左端射影は、任意のパラメーター射に厳密に自然。 -/
lemma edgewiseReflectedParameter_naturality {H K : SSet.{u}} (g : H ⟶ K) :
    SSet.opFunctor.map ((SSet.uliftFunctor.{u + 1, u}).map (edgewiseSubdivisionMap g)) ≫
      edgewiseReflectedParameter K =
    edgewiseReflectedParameter H ≫ (SSet.uliftFunctor.{u + 1, u}).map g := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro a
  rfl

/-- 共通 Hom 解像の左端を反転して、元の直接の Hom のパラメーターへ戻す射。 -/
def edgewiseReflectedHomParameter (X Y : SSet.{u}) :
    ((SSet.uliftFunctor.{u + 1, u}).obj
      (edgewiseSubdivision ((ihom X).obj Y))).op ⟶
        (SSet.uliftFunctor.{u + 1, u}).obj ((ihom X).obj Y) :=
  edgewiseReflectedParameter ((ihom X).obj Y)

/-- 同じパラメーターからの直接の作用は、共通解像の反転した豊穣作用そのもの。 -/
lemma edgewiseReflectedHomParameter_reverse (X Y : SSet.{u}) :
    edgewiseReflectedHomParameter X Y ≫
      leftPointHomReverseParameter (uncurry (𝟙 ((ihom X).obj Y))) =
    SSet.opFunctor.map ((SSet.uliftFunctor.{u + 1, u}).map
      (edgewiseOppositeKanEnrichedMap X Y)) := by
  have h : curry ((HomotopyLimits.oppositeTensorIso X ((ihom X).obj Y)).inv ≫
      SSet.opFunctor.map (uncurry (𝟙 ((ihom X).obj Y)))) =
      (HomotopyLimits.oppositeInternalHomIso X Y).hom := by
    apply uncurry_injective
    rw [uncurry_curry, oppositeInternalHomIso_uncurry]
    rfl
  have he : edgewiseOppositeKanEnrichedMap X Y =
      edgewiseLeft ((ihom X).obj Y) ≫ (HomotopyLimits.oppositeInternalHomIso X Y).hom := by
    apply uncurry_injective
    rw [edgewiseOppositeKanEnrichedMap, uncurry_curry,
      uncurry_natural_left, oppositeInternalHomIso_uncurry]
    rfl
  rw [leftPointHomReverseParameter, h, he]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro a
  rfl

end SerrePositivity.InfinityCategories
