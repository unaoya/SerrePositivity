module
public import SerrePositivity.InfinityCategories.DGNerve.FullSubcategory
public import SerrePositivity.InfinityCategories.DGNerve.HomotopyCategory
public import SerrePositivity.InfinityCategories.Core.HomotopyCategoryBridge
public import SerrePositivity.InfinityCategories.Core.InvertibleEdgeLifting

/-! # 充満 dg 部分圏の包含の h 上の忠実性

概要：充満 dg 部分圏の包含は通常の道の商によるホモトピー圏でも忠実。
方針：辺の代表を取り、H⁰ の比較と充満 dg 包含の忠実性で反映する。
規約：対象の閉性は不要。使われ方：D7 の周囲で計算した成分の反映。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.HomotopyComparison SSet
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] (P : D → Prop)

/-- 充満 dg 包含の h 上の通常の関手は忠実。 -/
instance fullInclusionHo_faithful :
    (hoFunctor.map (dgNerve.map (dgFullSubcategoryInclusion R D P))).toFunctor.Faithful where
  map_injective {x y} f g h := by
    obtain ⟨x⟩ := x
    obtain ⟨y⟩ := y
    obtain ⟨e, rfl⟩ := homotopyCategory_homMk_surjective _ _ f
    obtain ⟨d, rfl⟩ := homotopyCategory_homMk_surjective _ _ g
    have hh := congrArg (fun k => (toH0 R D).map
      ((pathToEdgeHomotopyCategory ((truncation 2).obj (dgNerve R D))).map k)) h
    apply (homotopyCategoryBridge (dgNerve R (DGFullSubcategory D P))).inverse.map_injective
    apply (toH0 R (DGFullSubcategory D P)).map_injective
    apply (dgFullSubcategoryInclusion R D P).onHomotopy.map_injective
    simp only [hoFunctor, Functor.toCatHom_toFunctor, SSet.mapHomotopyCategory,
      SSet.Truncated.mapHomotopyCategory_homMk, homotopyCategoryBridge,
      CategoryTheory.Equivalence.mk, pathToEdgeHomotopyCategory,
      SSet.Truncated.HomotopyCategory.lift_map_homMk] at hh ⊢
    change (dgFullSubcategoryInclusion R D P).onHomotopy.map
      ((toHomotopy R (DGFullSubcategory D P)).map (edgeClosed e)) =
        (dgFullSubcategoryInclusion R D P).onHomotopy.map
          ((toHomotopy R (DGFullSubcategory D P)).map (edgeClosed d))
    rw [dgFullSubcategoryInclusion_onHomotopy_map, dgFullSubcategoryInclusion_onHomotopy_map]
    change (toHomotopy R D).map (edgeClosed (e.map ((truncation 2).map
      (dgNerve.map (dgFullSubcategoryInclusion R D P))))) =
        (toHomotopy R D).map (edgeClosed (d.map ((truncation 2).map
          (dgNerve.map (dgFullSubcategoryInclusion R D P))))) at hh
    exact hh

end SerrePositivity.InfinityCategories
