module

public import SerrePositivity.InfinityCategories.HomotopyLimits.WeightedFunctor
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
概要：元の weighted sections と任意の内部 Hom の交換同型。
方針：重み付きパラメータの tensor 交換同型を、二つの実際の随伴の mate とする。
規約：Kan 性も小ささの条件も不要。同じ図式の全自然同型を構成する。
使われ方：Kan 複体の錐の元の比較から、全表現可能 Hom の極限判定へ移る。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits
variable {I : Type u} [SmallCategory I]

/-- 重みと追加パラメータの位置を交換する全図式の同型。 -/
def weightedParameterTensorIso (W : I ⥤ SSet.{u}) (X : SSet.{u}) :
    tensorLeft X ⋙ weightedParameterFunctor W ≅
      weightedParameterFunctor W ⋙
        (Functor.whiskeringRight I SSet.{u} SSet.{u}).obj (tensorLeft X) := by
  refine NatIso.ofComponents (fun A ↦ NatIso.ofComponents (fun i ↦
    (α_ (W.obj i) X A).symm ≪≫
      (tensorRight A).mapIso (β_ (W.obj i) X) ≪≫ (α_ X (W.obj i) A)) ?_) ?_
  · rename_i A
    intro i j f
    change (W.map f ▷ (X ⊗ A)) ≫ (α_ (W.obj j) X A).inv ≫
        ((β_ (W.obj j) X).hom ▷ A) ≫ (α_ X (W.obj j) A).hom =
      ((α_ (W.obj i) X A).inv ≫ ((β_ (W.obj i) X).hom ▷ A) ≫
        (α_ X (W.obj i) A).hom) ≫ (X ◁ (W.map f ▷ A))
    simp only [Category.assoc]
    rw [associator_inv_naturality_left_assoc, ← comp_whiskerRight_assoc,
      BraidedCategory.braiding_naturality_left, comp_whiskerRight_assoc,
      associator_naturality_middle]
  · intro A B f
    apply NatTrans.ext
    funext i
    change (W.obj i ◁ (X ◁ f)) ≫ (α_ (W.obj i) X B).inv ≫
        ((β_ (W.obj i) X).hom ▷ B) ≫ (α_ X (W.obj i) B).hom =
      ((α_ (W.obj i) X A).inv ≫ ((β_ (W.obj i) X).hom ▷ A) ≫
        (α_ X (W.obj i) A).hom) ≫ (X ◁ (W.obj i ◁ f))
    simp only [Category.assoc]
    rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc,
      associator_naturality_right]

/-- 同じ重み付き切断は、任意のパラメータからの内部 Hom と全自然に交換する。 -/
def weightedSectionsCotensorIso (W : I ⥤ SSet.{u}) (X : SSet.{u}) :
    weightedSectionsFunctor W ⋙ ihom X ≅
      (Functor.whiskeringRight I SSet.{u} SSet.{u}).obj (ihom X) ⋙
        weightedSectionsFunctor W :=
  conjugateIsoEquiv
    ((ihom.adjunction X).comp (weightedSectionsAdjunction W))
    ((weightedSectionsAdjunction W).comp ((ihom.adjunction X).whiskerRight I))
    (weightedParameterTensorIso W X).symm

/-- 交換同型の評価は、元の普遍切断と内部 Hom の評価の合成そのもの。 -/
lemma weightedSectionsCotensorIso_evaluation (W H : I ⥤ SSet.{u}) (X : SSet.{u}) (i : I) :
    uncurry (uncurry ((weightedSectionsCotensorIso W X).hom.app H ≫
      weightedSectionsπ W (H ⋙ ihom X) i)) =
        ((weightedParameterTensorIso W X).inv.app
          ((ihom X).obj (weightedSections W H))).app i ≫
        (W.obj i ◁ (ihom.ev X).app (weightedSections W H)) ≫
          uncurry (weightedSectionsπ W H i) := by
  have h := congrArg (fun η ↦ η.app i) (conjugateEquiv_counit
    ((ihom.adjunction X).comp (weightedSectionsAdjunction W))
    ((weightedSectionsAdjunction W).comp ((ihom.adjunction X).whiskerRight I))
    (weightedParameterTensorIso W X).inv H)
  change (X ◁ (W.obj i ◁ (weightedSectionsCotensorIso W X).hom.app H)) ≫
      (X ◁ uncurry (weightedSectionsπ W (H ⋙ ihom X) i)) ≫
        (ihom.ev X).app (H.obj i) =
      ((weightedParameterTensorIso W X).inv.app
        ((ihom X).obj (weightedSections W H))).app i ≫
        (W.obj i ◁ (ihom.ev X).app (weightedSections W H)) ≫
          uncurry (weightedSectionsπ W H i) at h
  simpa only [Functor.comp_obj, Functor.id_obj, uncurry_natural_left, uncurry_eq,
    MonoidalCategory.whiskerLeft_comp,
    Category.assoc] using h

/-- パラメータ交換後に重みを忘れることは、元のパラメータのまま重みを忘れること。 -/
@[reassoc] lemma weightedParameterTensorIso_inv_snd
    (W : I ⥤ SSet.{u}) (X A : SSet.{u}) (i : I) :
    ((weightedParameterTensorIso W X).inv.app A).app i ≫ snd (W.obj i) (X ⊗ A) =
      X ◁ snd (W.obj i) A := by
  change (α_ X (W.obj i) A).inv ≫ ((β_ (W.obj i) X).inv ▷ A) ≫
      (α_ (W.obj i) X A).hom ≫ snd (W.obj i) (X ⊗ A) = _
  apply CartesianMonoidalCategory.hom_ext <;> simp

/-- 元の錐の比較射に内部 Hom を適用すると、交換同型を通じて同じ Hom 錐の比較へ戻る。 -/
lemma weightedConeComparison_cotensor (W : I ⥤ SSet.{u}) {H : I ⥤ SSet.{u}}
    (c : Cone H) (X : SSet.{u}) :
    (ihom X).map (weightedConeComparison W c) ≫
        (weightedSectionsCotensorIso W X).hom.app H =
      weightedConeComparison W ((ihom X).mapCone c) := by
  apply weightedSections_hom_ext
  intro i
  change ((ihom X).map (weightedConeComparison W c) ≫
      (weightedSectionsCotensorIso W X).hom.app H) ≫
        weightedSectionsπ W (H ⋙ ihom X) i =
    weightedConeComparison W ((ihom X).mapCone c) ≫
        weightedSectionsπ W (H ⋙ ihom X) i
  apply uncurry_injective
  apply uncurry_injective
  rw [Category.assoc, uncurry_natural_left, uncurry_natural_left,
    weightedSectionsCotensorIso_evaluation]
  have hn := congrArg (fun η ↦ η.app i)
    ((weightedParameterTensorIso W X).inv.naturality
      ((ihom X).map (weightedConeComparison W c)))
  change (X ◁ (W.obj i ◁ (ihom X).map (weightedConeComparison W c))) ≫
      ((weightedParameterTensorIso W X).inv.app
        ((ihom X).obj (weightedSections W H))).app i =
    ((weightedParameterTensorIso W X).inv.app ((ihom X).obj c.pt)).app i ≫
      (W.obj i ◁ (X ◁ (ihom X).map (weightedConeComparison W c))) at hn
  rw [← Category.assoc, hn]
  simp only [Category.assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, ihom.ev_naturality,
    MonoidalCategory.whiskerLeft_comp_assoc, ← uncurry_natural_left,
    weightedConeComparison_π, uncurry_curry]
  erw [whiskerLeft_snd_assoc]
  erw [weightedParameterTensorIso_inv_snd_assoc]
  rw [weightedConeComparison_π, uncurry_curry]
  change _ = uncurry (snd (W.obj i) ((ihom X).obj c.pt) ≫ (ihom X).map (c.π.app i))
  rw [uncurry_eq, MonoidalCategory.whiskerLeft_comp, Category.assoc,
    ihom.ev_naturality]

end SerrePositivity.InfinityCategories.F2.Presentable
