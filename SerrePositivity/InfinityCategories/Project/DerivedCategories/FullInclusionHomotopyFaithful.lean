module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FullSubcategory
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomotopyCategory
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.HomotopyCategoryBridge
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting

/-! # 充満 dg 部分圏の包含の h 上の忠実性

概要：充満 dg 部分圏の包含は通常の道の商によるホモトピー圏でも忠実。
方針：辺の代表を取り、H⁰ の比較と充満 dg 包含の忠実性で反映する。
規約：対象の閉性は不要。使われ方：D7 の周囲で計算した成分の反映。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] (P : D → Prop)

/-- 充満 dg 包含の h 上の通常の関手は忠実。 -/
instance fullInclusionHo_faithful :
    (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R D P))).toFunctor.Faithful where
  map_injective {x y} f g h := by
    obtain ⟨x⟩ := x
    obtain ⟨y⟩ := y
    obtain ⟨e, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective _ _ f
    obtain ⟨d, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective _ _ g
    have hh := congrArg (fun k => (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.toH0 R D).map
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.pathToEdgeHomotopyCategory ((truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D))).map k)) h
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyCategoryBridge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGFullSubcategory D P))).inverse.map_injective
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.toH0 R (DGFullSubcategory D P)).map_injective
    apply (_root_.SerrePositivity.DifferentialGraded.dgFullSubcategoryInclusion R D P).onHomotopy.map_injective
    simp only [hoFunctor, Functor.toCatHom_toFunctor, SSet.mapHomotopyCategory,
      SSet.Truncated.mapHomotopyCategory_homMk, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyCategoryBridge,
      CategoryTheory.Equivalence.mk, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.pathToEdgeHomotopyCategory,
      SSet.Truncated.HomotopyCategory.lift_map_homMk] at hh ⊢
    change (_root_.SerrePositivity.DifferentialGraded.dgFullSubcategoryInclusion R D P).onHomotopy.map
      ((toHomotopy R (DGFullSubcategory D P)).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed e)) =
        (_root_.SerrePositivity.DifferentialGraded.dgFullSubcategoryInclusion R D P).onHomotopy.map
          ((toHomotopy R (DGFullSubcategory D P)).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed d))
    rw [_root_.SerrePositivity.DifferentialGraded.dgFullSubcategoryInclusion_onHomotopy_map, _root_.SerrePositivity.DifferentialGraded.dgFullSubcategoryInclusion_onHomotopy_map]
    change (toHomotopy R D).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed (e.map ((truncation 2).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R D P))))) =
        (toHomotopy R D).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed (d.map ((truncation 2).map
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R D P))))) at hh
    exact hh

end SerrePositivity.InfinityCategories.Project.DerivedCategories
