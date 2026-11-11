module

public import SerrePositivity.KST.Spectra.RawSpectrumPointedCompositionNaturality
public import SerrePositivity.KST.Spectra.PointedWeightedEndFunctor
public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeSymmetry

/-!
概要：BF 源の全 Hom パラメータによる、元の weighted Hom end への合成作用。
方針：係数の合成を curry して自然変換へ束ね、end の関手と内部 Hom の交換を使う。
規約：元の係数の合成から構成し、各射影でその公式を検証する。
使われ方：Hom–end 交換の豊穣自然性と γ3 への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed

namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
local instance weightedCompositionSelfEnrichment :
    EnrichedOrdinaryCategory PointedSimplicialSet.{u} PointedSimplicialSet.{u} :=
  enrichedOrdinaryCategorySelf PointedSimplicialSet.{u}

/-- 点つき Hom の合成を curry した、標的全体の自然変換。 -/
def compositionTransformation (X Y : OmegaSpectrum.{u}) :
    pointedFunctor Y ⟶ pointedFunctor X ⋙ ihom (pointedSpace X Y.toKanSequence) where
  app Z := curry (pointedComposition X Y Z)
  naturality Z T p := by
    change pointedPost Y p ≫ curry (pointedComposition X Y T) =
      curry (pointedComposition X Y Z) ≫
        (ihom (pointedSpace X Y.toKanSequence)).map (pointedPost X p)
    rw [← curry_natural_left, ← curry_natural_right]
    apply congrArg curry
    simpa only [id_tensorHom] using (pointedComposition_post X Y p).symm

/-- end–内部 Hom 交換の逆射の各射影での公式。 -/
lemma weightedCotensor_inv_π {I : Type u} [SmallCategory I]
    (K : PointedSimplicialSet.{u}) (W : I ⥤ SSet.{u})
    (D : I ⥤ PointedSimplicialSet.{u}) (i : I) :
    (PointedWeightedEnd.cotensorIso K W D).inv ≫
        (ihom K).map (end_.π (PointedWeightedEnd.diagram W D) i) =
      end_.π (PointedWeightedEnd.diagram W (D ⋙ ihom K)) i ≫
        (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso K (PointedObject.adjoin (W.obj i)) (D.obj i)).inv := by
  apply (cancel_epi (PointedWeightedEnd.cotensorIso K W D).hom).mp
  rw [Iso.hom_inv_id_assoc, ← Category.assoc, PointedWeightedEnd.cotensorIso_π,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- 係数の合成の自然変換と end–内部 Hom 交換から得る、end 上の全 Hom の作用。 -/
def weightedComposition {I : Type u} [SmallCategory I] (X Y : OmegaSpectrum.{u})
    (W : I ⥤ SSet.{u}) (D : I ⥤ KanSequence.{u}) :
    pointedSpace X Y.toKanSequence ⊗ PointedWeightedEnd.obj W (D ⋙ pointedFunctor Y) ⟶
      PointedWeightedEnd.obj W (D ⋙ pointedFunctor X) :=
  uncurry (PointedWeightedEnd.map W (Functor.whiskerLeft D (compositionTransformation X Y)) ≫
    (PointedWeightedEnd.cotensorIso (pointedSpace X Y.toKanSequence) W
      (D ⋙ pointedFunctor X)).inv)

/-- end 上の作用は、元の係数の合成・各射影・strength で計算される。 -/
@[reassoc]
lemma weightedComposition_π {I : Type u} [SmallCategory I] (X Y : OmegaSpectrum.{u})
    (W : I ⥤ SSet.{u}) (D : I ⥤ KanSequence.{u}) (i : I) :
    weightedComposition X Y W D ≫ end_.π (PointedWeightedEnd.diagram W (D ⋙ pointedFunctor X)) i =
      (𝟙 (pointedSpace X Y.toKanSequence) ⊗ₘ
        end_.π (PointedWeightedEnd.diagram W (D ⋙ pointedFunctor Y)) i) ≫
        _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map (pointedSpace X Y.toKanSequence)
          (PointedObject.adjoin (W.obj i)) (pointedSpace Y (D.obj i)) ≫
          (ihom (PointedObject.adjoin (W.obj i))).map
            (pointedComposition X Y (D.obj i)) := by
  rw [weightedComposition, ← uncurry_natural_right, Category.assoc, weightedCotensor_inv_π]
  rw [← Category.assoc]
  erw [PointedWeightedEnd.map_π]
  rw [Category.assoc]
  change uncurry (end_.π (PointedWeightedEnd.diagram W (D ⋙ pointedFunctor Y)) i ≫
    (ihom (PointedObject.adjoin (W.obj i))).map (curry (pointedComposition X Y (D.obj i))) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso (pointedSpace X Y.toKanSequence)
      (PointedObject.adjoin (W.obj i)) (pointedSpace X (D.obj i))).inv) = _
  rw [← _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.hom_eq_inv, ← _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.curry_strength,
    uncurry_natural_left, uncurry_curry, id_tensorHom]
  rfl

end SerrePositivity.KST.Spectra.RawSpectrumMapping
