module

public import SerrePositivity.KST.Spectra.TotalizationBousfieldKanComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedRestriction

/-!
概要：通常 Tot を宇宙を合わせた標準単体の重み付き end と厳密に同定する。
方針：AsSmall の上昇・下降で各成分を付け替え、end の普遍性で両逆を示す。
規約：Kan 性を仮定しない通常の単体集合の同型。
使われ方：Goerss–Jardine VIII §1。構成済みの比較射を重みの制限の一般的な充填へ接続する。
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed SSet

open scoped MonoidalClosed

namespace SerrePositivity.KST.Spectra.CosimplicialTotalization
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 標準単体のパラメーター付き族を AsSmall 上に付け替える。 -/
def smallFamily (X : CosimplicialObject SSet.{u}) :
    (AsSmall.down ⋙ stdSimplex) ⊗ (Functor.const _).obj (obj X) ⟶ AsSmall.down ⋙ X where
  app j := MonoidalClosed.uncurry (π X (AsSmall.down.obj j))
  naturality i j f := by
    change (stdSimplex.map (AsSmall.down.map f) ▷ obj X) ≫ _ = _
    rw [← uncurry_pre_app, ← uncurry_natural_right]
    exact congrArg MonoidalClosed.uncurry (condition X (AsSmall.down.map f)).symm

/-- 通常 Tot から AsSmall 上の標準単体 end への実際の付け替え。 -/
def toSmallEnd (X : CosimplicialObject SSet.{u}) :
    obj X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections (AsSmall.down ⋙ stdSimplex) (AsSmall.down ⋙ X) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift (smallFamily X)

@[reassoc]
lemma toSmallEnd_π (X : CosimplicialObject SSet.{u}) (j : AsSmall.{u} SimplexCategory) :
    toSmallEnd X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ (AsSmall.down ⋙ stdSimplex) (AsSmall.down ⋙ X) j =
      π X (AsSmall.down.obj j) := by
  rw [toSmallEnd, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift_π]
  exact curry_uncurry _

/-- AsSmall 上の end の族を元の余単体圏に戻す。 -/
def fromSmallFamily (X : CosimplicialObject SSet.{u}) :
    SimplexTensorBoundary.diagram
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections (AsSmall.down ⋙ stdSimplex) (AsSmall.down ⋙ X)) ⟶ X where
  app j := MonoidalClosed.uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ
    (AsSmall.down ⋙ stdSimplex) (AsSmall.down ⋙ X) (AsSmall.up.obj j))
  naturality i j f := by
    change (stdSimplex.map f ▷ _) ≫ _ = _
    rw [← uncurry_pre_app, ← uncurry_natural_right]
    exact congrArg MonoidalClosed.uncurry
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections_condition (AsSmall.down ⋙ stdSimplex) (AsSmall.down ⋙ X)
        (AsSmall.up.map f)).symm

/-- 通常 Tot と、宇宙を合わせた標準単体 end の標準同型。 -/
def smallEndIso (X : CosimplicialObject SSet.{u}) :
    obj X ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections (AsSmall.down ⋙ stdSimplex) (AsSmall.down ⋙ X) where
  hom := toSmallEnd X
  inv := lift (fromSmallFamily X)
  hom_inv_id := by
    apply end_.hom_ext
    intro j
    change (toSmallEnd X ≫ lift (fromSmallFamily X)) ≫ π X j = 𝟙 _ ≫ π X j
    rw [Category.assoc, lift_π]
    change toSmallEnd X ≫ curry (MonoidalClosed.uncurry
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ _ _ (AsSmall.up.obj j))) = _
    rw [curry_uncurry, toSmallEnd_π, Category.id_comp]
    rfl
  inv_hom_id := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections_hom_ext
    intro j
    rw [Category.assoc, toSmallEnd_π]
    change lift (fromSmallFamily X) ≫ π X (AsSmall.down.obj j) = 𝟙 _ ≫ _
    rw [lift_π]
    change curry (MonoidalClosed.uncurry
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ _ _ (AsSmall.up.obj (AsSmall.down.obj j)))) = _
    rw [curry_uncurry, Category.id_comp]
    rfl

/-- 構成済みの Tot 比較は終頂点の重みの射への前合成そのもの。 -/
lemma bousfieldKanComparison_eq_weightedPre (X : CosimplicialObject SSet.{u}) :
    bousfieldKanComparison X = (smallEndIso X).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre CosimplicialLastVertex.weightMap (AsSmall.down ⋙ X) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections_hom_ext
  intro j
  rw [bousfieldKanComparison_π, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre_π,
    ← Category.assoc]
  dsimp only [smallEndIso]
  erw [toSmallEnd_π]
  rfl

end
end SerrePositivity.KST.Spectra.CosimplicialTotalization
