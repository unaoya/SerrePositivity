module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorSourceNuRoof
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.DGComposition.DGUniverseLiftFunctor
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeVerdierPresentation

/-!
概要：元対角・核比較・二つの増大を同じ固定 S の全四角形に保持する。
方針：構成済みの厳密 dg 可換式を持ち上げ、Sp 正本の coherent 四角形構成へ渡す。
規約：元始域は増大屋根の終端であり、S 内の逆増大を要求しない。
使われ方：d④ の元対角始域の屋根と指定境界の比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "A" => DGSmallPerfectBase R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R (DGOdotInput.source d))
local notation "B" => DGOdotGluing R d
local notation "δ" => DGLaxQuotientEndInput.diagonal (dgOdotQuotientInput R d)
local notation "P" => dgQuotientImage R (δ)

/-- 概要：同じ元対角・核比較・二つの増大は固定 S 内で厳密可換。
方針：持ち上げの合成保存と元 dg 可換式を使用する。
規約：同じ四つの入力関手を保持する。使われ方：実元始域屋根の比較面。 -/
lemma dgOdotMilnorSourceSquare_comm :
    (dgOdotMilnorSourceKernelInputMap R d ≫ dgOdotMilnorFlatKernelInputMap R d) ≫
      dgOdotMilnorAugmentationInputMap R d =
        dgOdotMilnorSourceAugmentationInputMap R d ≫ dgOdotDiagonalInputMap R d := by
  apply ULift.ext
  change ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, u + 1, u + 1, u + 1, u + 1}
    (dgOdotMilnorSourceKernelDGMap R d)).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, u + 1, u + 1, u + 1, u + 1}
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientThickFlatKernelInclusion R (B) (P)))).comp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, u + 1, u + 1, u + 1, u + 1}
      (DGCategoryCellResolution.augmentation R (B))) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, u + 1, u + 1, u + 1, u + 1}
      (DGCategoryCellResolution.augmentation R (A))).comp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, u + 1, u + 1, u + 1, u + 1} (δ))
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor_comp, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor_comp,
    ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor_comp]
  apply congrArg (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, u + 1, u + 1, u + 1, u + 1})
  rw [strictDGFunctor_comp_assoc]
  exact dgOdotMilnorSourceKernelDGMap_augmentation R d

/-- 概要：同じ元始域増大屋根は四辺を厳密に保つ実 S 比較面を持つ。
方針：同じ可換式を coherent nerve の四角形へ実現する。
規約：元対角と両増大の全一単体を保持する。使われ方：完備化付き相対面の始域比較。 -/
theorem exists_dgOdotMilnorSourceSquare :
    ∃ F : (Δ[1] ⊗ Δ[1] : SSet.{u + 2}) ⟶ dgKInputInfinity.{u, u + 1} R,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ F = SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotMilnorSourceKernelInputMap R d ≫
          dgOdotMilnorFlatKernelInputMap R d)).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ F = SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotDiagonalInputMap R d)).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ F = SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotMilnorSourceAugmentationInputMap R d)).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ F = SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotMilnorAugmentationInputMap R d)).edge := by
  obtain ⟨F, hb, hr, hl, ht⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.exists_coherentSquare_of_comm
    (dgOdotMilnorSourceKernelInputMap R d ≫ dgOdotMilnorFlatKernelInputMap R d)
    (dgOdotMilnorAugmentationInputMap R d)
    (dgOdotMilnorSourceAugmentationInputMap R d) (dgOdotDiagonalInputMap R d)
    (dgOdotMilnorSourceSquare_comm R d)
  exact ⟨F, hb, ht, hl, hr⟩

end SerrePositivity.KST.SConstruction
