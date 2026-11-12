module
public import SerrePositivity.KST.Fibration.VerdierFullSLowerShortFaces
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CompositionTriangleFamily

/-!
概要：指定 Verdier 下側の実三角柱を、元の短辺を固定した全三角形空間の実辺にする。
方針：二短辺の固定を内ホーンの積 pushout で貼り、F1 正本の固定延長 fiber へ戻す。
規約：元の全三角柱・短辺を厳密に回収する。共有対角の固定や上側との整合は結論しない。
使われ方：K-6 c4 の上下二胞体を同じ対角族で貼る際の、下側の指定境界付き入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u})

/-- 元の下側二胞体の二短辺を、そのまま同じ内ホーンへ制限する。 -/
def verdierFullSLowerHorn : (horn 2 1 : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  (horn 2 1).ι ≫ SSet.yonedaEquiv.symm (verdierFullSLowerSimplex d)

/-- 同じ下側実三角柱は、元の二短辺の内ホーン全体を全時刻固定する。 -/
theorem verdierFullSLowerDeformation_horn :
    ((horn 2 1).ι ▷ (Δ[1] : SSet.{u + 1})) ≫ (verdierFullSLowerDeformation d).h =
      fst (horn 2 1 : SSet.{u + 1}) Δ[1] ≫ verdierFullSLowerHorn d := by
  apply (horn₂₁.isPushout.map (tensorRight (Δ[1] : SSet.{u + 1}))).hom_ext
  · change (horn₂₁.ι₀₁ ▷ (Δ[1] : SSet.{u + 1})) ≫
        ((horn 2 1).ι ▷ Δ[1]) ≫ (verdierFullSLowerDeformation d).h =
      (horn₂₁.ι₀₁ ▷ Δ[1]) ≫ fst (horn 2 1 : SSet.{u + 1}) Δ[1] ≫
        verdierFullSLowerHorn d
    rw [← Category.assoc, ← comp_whiskerRight, horn.ι_ι,
      verdierFullSLowerDeformation_first]
    simp only [verdierFullSLowerHorn, ← Category.assoc, whiskerRight_fst]
    simp only [Category.assoc, horn.ι_ι]
  · change (horn₂₁.ι₁₂ ▷ (Δ[1] : SSet.{u + 1})) ≫
        ((horn 2 1).ι ▷ Δ[1]) ≫ (verdierFullSLowerDeformation d).h =
      (horn₂₁.ι₁₂ ▷ Δ[1]) ≫ fst (horn 2 1 : SSet.{u + 1}) Δ[1] ≫
        verdierFullSLowerHorn d
    rw [← Category.assoc, ← comp_whiskerRight, horn.ι_ι,
      verdierFullSLowerDeformation_last]
    simp only [verdierFullSLowerHorn, ← Category.assoc, whiskerRight_fst]
    simp only [Category.assoc, horn.ι_ι]

/-- 元の短辺を固定した全三角形空間は可縮 Kan。 -/
theorem verdierFullSLowerExtension_isContractibleKan :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.innerTriangleExtensionSpace (verdierFullSLowerHorn d)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.innerTriangleExtensionSpace_isContractibleKan _

/-- 同じ元の三角柱を、指定短辺の延長空間の実辺として読む。 -/
def verdierFullSLowerDeformationFamily :
    (Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.innerTriangleExtensionSpace (verdierFullSLowerHorn d) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.innerTriangleExtensionCurry (verdierFullSLowerHorn d)
    (verdierFullSLowerDeformation d).h (verdierFullSLowerDeformation_horn d)

/-- 同じ固定延長空間の実辺の評価は、元の全三角柱そのもの。 -/
theorem verdierFullSLowerDeformationFamily_recovery :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.innerTriangleExtensionUncurry (verdierFullSLowerDeformationFamily d) =
      (verdierFullSLowerDeformation d).h :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.innerTriangleExtensionUncurry_curry _ _ _

end SerrePositivity.KST.Fibration
