module
public import SerrePositivity.EInfinity.FrameHom.MixedNerveNatTrans
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.NerveCoconePrism

/-!
概要：混合宇宙の通常余錐の全 join prism は、元の自然変換円柱そのものと一致する。
方針：既存の Hom 持ち上げ・同じ自然変換・同じ上下射を保持して余錐比較を移す。
規約：元の全単体の厳密な等式。使われ方：正規化 tensor の元の augmentation との比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.FrameHom.MixedNerve
open SerrePositivity.InfinityCategories
open CategoryTheory Limits SSet MonoidalCategory
open scoped Simplicial
variable {I C : Type (u + 1)} [Category.{u} I] [Category.{u} C] {F : I ⥤ C}

def liftedCocone (c : Cocone F) : Cocone (lifted F) where
  pt := ULiftHom.objUp c.pt
  ι := liftedNatTrans c.ι

def coconeJoin (c : Cocone F) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (nerve I) (Δ[0] : SSet.{u + 1}) ⟶ nerve C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (up I) (𝟙 Δ[0]) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCoconeEquiv (liftedCocone c)).val ≫ down C

lemma coconePrism_eq_homotopy (c : Cocone F) :
    (β_ (nerve I) (Δ[1] : SSet.{u + 1})).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism (nerve I) ≫
      coconeJoin c = (homotopy c.ι).h := by
  have hn := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism_naturality (up I)
  have hb : (up I ▷ (Δ[1] : SSet.{u + 1})) ≫
      (β_ (nerve (ULiftHom.{u + 1} I)) (Δ[1] : SSet.{u + 1})).hom =
      (β_ (nerve I) (Δ[1] : SSet.{u + 1})).hom ≫ (Δ[1] ◁ up I) := rfl
  change (β_ (nerve I) (Δ[1] : SSet.{u + 1})).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism (nerve I) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (up I) (𝟙 Δ[0]) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCoconeEquiv (liftedCocone c)).val ≫ down C) =
      (up I ▷ (Δ[1] : SSet.{u + 1})) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy (liftedNatTrans c.ι)).h ≫ down C
  have hc : (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy (liftedNatTrans c.ι)).h =
      (β_ (nerve (ULiftHom.{u + 1} I)) (Δ[1] : SSet.{u + 1})).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCoconeEquiv (liftedCocone c)).val := by
    exact (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nerveCoconePrism_eq_natTrans (lifted F) (liftedCocone c)).symm
  rw [hc]
  simp only [← Category.assoc]
  rw [hb]
  simp only [Category.assoc]
  rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism _), ← hn]
  simp only [Category.assoc]
end SerrePositivity.EInfinity.FrameHom.MixedNerve
