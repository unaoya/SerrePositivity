module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.WeightedColimitAugmentation
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.WeightedConeOppositeComparison
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ReflectedBousfieldKanColimit
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedColimit
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedColimitHom
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedSections
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedSectionsOpposite

/-!
概要：通常の余錐の反変 Hom 錐を、augmentation の前合成と coend の Hom 同型で表示する。
方針：各重み付き脚で評価し、二度の curry を戻して元の余錐の脚を回収する。
規約：重みは任意、値や標的の Kan 性は不要。
使われ方：通常の filtered colimit 余錐自体の native な普遍性。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

variable {I : Type u} [SmallCategory I] {F : I ⥤ SSet.{u}}

/-- 概要：余錐の頂点から標的への Hom は反変係数の通常の錐を定める。
方針：余錐の各脚による前合成を錐の脚にする。
規約：内部 Hom を実際の単体集合として使う。使われ方：重み付き切断との比較。 -/
def coconeHomCone (c : Cocone F) (Y : SSet.{u}) : Cone (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomDiagram F Y) where
  pt := (ihom c.pt).obj Y
  π := {
    app i := (pre (c.ι.app i.unop)).app Y
    naturality i j f := by
      change (pre (c.ι.app j.unop)).app Y =
        (pre (c.ι.app i.unop)).app Y ≫ (pre (F.map f.unop)).app Y
      rw [← NatTrans.comp_app, ← pre_map, c.w f.unop] }

/-- 概要：augmentation の前合成は coend の Hom 同型の下で元の Hom 錐の比較となる。
方針：end の各射影で二度 curry を取り、augmentation の脚の式を使う。
規約：標準比較射そのものの等式。使われ方：反転した表現可能比較との照合。 -/
lemma coconeHomCone_weightedComparison (W : Iᵒᵖ ⥤ SSet.{u}) (c : Cocone F)
    (Y : SSet.{u}) :
    (pre (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitAugmentation W c)).app Y ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomComparison W F Y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison W (coconeHomCone c Y) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections_hom_ext
  intro i
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomComparison_π, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison_π]
  change (pre (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitAugmentation W c)).app Y ≫
    curry (curry ((α_ (F.obj i.unop) (W.obj i) _).inv ≫
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι W F i.unop ▷ _) ≫ (ihom.ev (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit W F)).app Y)) =
    curry (snd (W.obj i) ((ihom c.pt).obj Y) ≫ (pre (c.ι.app i.unop)).app Y)
  rw [← curry_natural_left, ← curry_natural_left]
  conv_rhs => rw [← curry_uncurry ((pre (c.ι.app i.unop)).app Y), ← curry_natural_left]
  apply congrArg curry
  apply congrArg curry
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    id_tensor_pre_app_comp_ev, ← comp_whiskerRight_assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitι_augmentation,
    comp_whiskerRight_assoc, uncurry_pre]
  rfl

/-- 概要：反転した augmentation の Hom 比較は反転 Hom 錐の標準比較。
方針：非反転の脚の公式を反転し、end の反転同型の比較則を使う。
規約：係数と標的は任意。使われ方：N の表現可能な比較への移送。 -/
lemma coconeHomCone_reflectedWeightedComparison (W : Iᵒᵖ ⥤ SSet.{u}) (c : Cocone F)
    (Y : SSet.{u}) :
    SSet.opFunctor.map ((pre (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitAugmentation (W ⋙ SSet.opFunctor) c)).app Y) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.reflectedWeightedColimitHomIso W F Y).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison W (SSet.opFunctor.mapCone (coconeHomCone c Y)) := by
  change SSet.opFunctor.map _ ≫ SSet.opFunctor.map
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomComparison (W ⋙ SSet.opFunctor) F Y) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedSectionsReflectedIso W (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomDiagram F Y)).hom = _
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, coconeHomCone_weightedComparison]
  exact _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.WeightedConeOppositeComparison.weightedConeComparison_reflected W (coconeHomCone c Y)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
