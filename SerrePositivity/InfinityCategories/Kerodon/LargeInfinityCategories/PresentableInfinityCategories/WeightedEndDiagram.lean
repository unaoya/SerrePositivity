module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedFunctor
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
概要：既存の weighted sections を、同じ multicospan 上の通常の極限関手で表す。
方針：内部 Hom の対角成分と自然性の二つの射を、図式について関手的に束ねる。
規約：値だけでなく、元の weightedSectionsMap 自身を比較する。
使われ方：小さい極限と内部 Hom の μ-filtered 保存を合成する。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
variable {I : Type u} [SmallCategory I]

/-- 元の重み付き end を計算する multicospan の、図式に関する同じ誘導射。 -/
def weightedEndDiagramMap (W : I ⥤ SSet.{u}) {H H' : I ⥤ SSet.{u}} (η : H ⟶ H') :
    (multicospanIndexEnd (Enriched.FunctorCategory.diagram SSet.{u} W H)).multicospan ⟶
      (multicospanIndexEnd (Enriched.FunctorCategory.diagram SSet.{u} W H')).multicospan where
  app x := match x with
    | .left i => (ihom (W.obj i)).map (η.app i)
    | .right f => (ihom (W.obj f.left)).map (η.app f.right)
  naturality {x y} f := by
    cases f with
    | id x => simp
    | fst f =>
      dsimp only [multicospanShapeEnd, MulticospanIndex.multicospan, multicospanIndexEnd,
        Enriched.FunctorCategory.diagram, Functor.comp_obj, Functor.comp_map,
        Functor.whiskeringLeft, Functor.op_obj, eHomFunctor]
      simp only [enrichedOrdinaryCategorySelf_eHomWhiskerLeft]
      change (ihom (W.obj f.left)).map (H.map f.hom) ≫
        (ihom (W.obj f.left)).map (η.app f.right) =
          (ihom (W.obj f.left)).map (η.app f.left) ≫
            (ihom (W.obj f.left)).map (H'.map f.hom)
      rw [← Functor.map_comp, η.naturality, Functor.map_comp]
    | snd f =>
      exact ((pre (W.map f.hom)).naturality (η.app f.right)).symm

/-- 元の重み付き切断を計算する、一つの厳密な multicospan 図式の関手。 -/
def weightedEndDiagramFunctor (W : I ⥤ SSet.{u}) : (I ⥤ SSet.{u}) ⥤
    WalkingMulticospan (multicospanShapeEnd I) ⥤ SSet.{u} where
  obj H := (multicospanIndexEnd (Enriched.FunctorCategory.diagram SSet.{u} W H)).multicospan
  map η := weightedEndDiagramMap W η
  map_id H := by
    ext x
    cases x <;> simp [weightedEndDiagramMap] <;> rfl
  map_comp η ε := by
    ext x
    cases x <;> simp [weightedEndDiagramMap] <;> rfl

/-- 元の weighted sections と、同じ図式の通常の極限との全自然な比較。 -/
def weightedSectionsLimitIso (W : I ⥤ SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsFunctor W ≅ weightedEndDiagramFunctor W ⋙ lim :=
  NatIso.ofComponents (fun H ↦ Iso.refl _) (by
    intro H H' η
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections_hom_ext
    intro i
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap W η ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ W H' i =
      (lim.map (weightedEndDiagramMap W η)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ W H' i
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap_π]
    exact (limit.map_π (weightedEndDiagramMap W η) (WalkingMulticospan.left i)).symm)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
