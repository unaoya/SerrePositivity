module
public import SerrePositivity.KST.SConstruction.ExInfinityPointedFamilies
public import SerrePositivity.KST.SConstruction.PointedSSetWhisker
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.StrictSimplicialTransformation

/-! # 同じ Ex∞ 単位の標準点つき全 Hom 自然性
概要：元の Ex∞ 単位は、標準点つき厳密豊穣関手の全 Hom に自然。
方針：元の全族の作用式を basedHom 包含と閉評価で反映する。
規約：全高次パラメータを保持。使われ方：関手的 BF 押し出し候補の Kan 値化。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet

/-- 同じ Ex∞ 単位の元の成分は、標準 basedHom の前後合成に厳密に自然。 -/
lemma exInfinityPointedUnit_whisker (X Y : PointedSSetObject.{u}) :
    eHomWhiskerLeft SSet X
        (show Y ⟶ exInfinityPointedEnrichedFunctor.obj Y from exInfinityPointedUnit Y) =
      exInfinityPointedEnrichedFunctor.map X Y ≫
        eHomWhiskerRight SSet
          (show X ⟶ exInfinityPointedEnrichedFunctor.obj X from exInfinityPointedUnit X)
          (exInfinityPointedEnrichedFunctor.obj Y) := by
  rw [pointedSSetObject_whiskerLeft, pointedSSetObject_whiskerRight]
  apply (cancel_mono (PointedObject.basedHomι X.obj
    (exInfinityPointedEnrichedFunctor.obj Y).obj)).mp
  apply uncurry_injective
  have h := exInfinityPointedFamily_unit_action X Y (𝟙 _)
  simp only [Category.id_comp] at h
  rw [Category.assoc, pointedFamily_pre_evaluation]
  have hp := pointedFamilyPost_evaluation X.obj Y.obj
    (exInfinityPointedEnrichedFunctor.obj Y).obj (𝟙 _) (exInfinityPointedUnit Y)
  simp only [Category.id_comp] at hp
  exact hp.trans h.symm

/-- 同じ元の豊穣関手へ前合成した Ex∞ 単位も、全 Hom に自然。 -/
lemma enrichedExInfinityPointedUnit_whisker
    {C : Type v} [EnrichedCategory SSet.{u} C]
    (F : EnrichedFunctor SSet.{u} C PointedSSetObject.{u}) (X Y : C) :
    F.map X Y ≫ eHomWhiskerLeft SSet (F.obj X)
        (show F.obj Y ⟶ (F.comp SSet exInfinityPointedEnrichedFunctor).obj Y from
          exInfinityPointedUnit (F.obj Y)) =
      (F.comp SSet exInfinityPointedEnrichedFunctor).map X Y ≫
        eHomWhiskerRight SSet
          (show F.obj X ⟶ (F.comp SSet exInfinityPointedEnrichedFunctor).obj X from
            exInfinityPointedUnit (F.obj X))
          ((F.comp SSet exInfinityPointedEnrichedFunctor).obj Y) := by
  exact (congrArg (fun q => F.map X Y ≫ q)
    (exInfinityPointedUnit_whisker (F.obj X) (F.obj Y))).trans
      (Category.assoc _ _ _).symm

/-- 同じ単位の実成分を持つ、任意の標準点つき厳密豊穣関手の Ex∞ 比較。 -/
def enrichedExInfinityPointedUnitTransformation
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (F : EnrichedFunctor SSet.{u} C PointedSSetObject.{u}) :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) F
      (F.comp SSet exInfinityPointedEnrichedFunctor) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformationOfWhisker _ _ (fun X => exInfinityPointedUnit (F.obj X))
    (enrichedExInfinityPointedUnit_whisker F)

end SerrePositivity.KST.SConstruction
