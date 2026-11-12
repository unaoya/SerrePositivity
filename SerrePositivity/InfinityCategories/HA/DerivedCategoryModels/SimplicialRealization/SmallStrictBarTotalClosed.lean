module

public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarThetaValues
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarTotalDifferential
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarTotalComposition
import all SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarTotalColumns

/-!
# 指定した実 bar 比較の閉性

## 概要
元の全単体列から指定した次数零の要素の微分は零である。

## 方針
列の微分と同じ theta の後合成を全ての列で比較し、MC の Hom 次数同値へ戻す。

## 規約
閉性を入力とせず、既に指定した同じ要素を用いる。

## 使われ方
HA 1.2.4。native coherent bar と実現複体の同じ比較射。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open HomologicalComplex CochainComplex HomComplex SerrePositivity.DifferentialGraded
open scoped _root_.Simplicial
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.HomologicalAlgebra
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
variable (A : Type u) [CommRing A] {J : Type} [SmallCategory J]

/-- 元の各列の微分は、同じ theta の列を比較した値である。 -/
theorem smallStrictBarTotalColumn_d (F : J ⥤ ModuleCategory A PUnit.{1})
    (s : dgCoherentBarIndex ((SSet.uliftFunctor.{u, 0}).obj (nerve J))) :
    (moduleHom A PUnit.{1}
      (ForgetEnrichment.to (Complex A) (dgCoherentBarFamily A PUnit.{1} (smallStrictBarDiagram A F) s))
      (smallStrictBarTotalTarget A F)).d 0 1 (smallStrictBarTotalColumn A F s) =
    compose A (D := RightModule A PUnit.{1})
      (x := ForgetEnrichment.to (Complex A)
        (dgCoherentBarFamily A PUnit.{1} (smallStrictBarDiagram A F) s))
      (y := ForgetEnrichment.to (Complex A)
        (dgCoherentBarGraded A PUnit.{1} (smallStrictBarDiagram A F)))
      (z := smallStrictBarTotalTarget A F) (smallStrictBarTotalGradedElement A F)
      (dgCoherentBarColumn A PUnit.{1} (smallStrictBarDiagram A F) s) (add_zero 1) := by
  apply moduleHomElement_ext A PUnit.{1}
  intro x
  cases x
  apply (smallStrictBarTotalColumn_point_d A F s).trans
  rcases s with ⟨n, s⟩
  cases n with
  | zero =>
    simp only [dgCoherentBarColumn, compose_zero, map_zero]
    change unsignedLeftShift (δ 0 1 (smallStrictBarUnshiftedColumn A F ⟨0, s⟩)) 0 1 _ = 0
    rw [smallStrictBarUnshiftedColumn_zero_closed]
    simp [unsignedLeftShift]
  | succ n => exact (smallStrictBarColumn_post_positive A F n s).symm

/-- 元の graded 比較の微分は、同じ theta の後合成に一致する。 -/
theorem smallStrictBarTotalGradedElement_d (F : J ⥤ ModuleCategory A PUnit.{1}) :
    (moduleHom A PUnit.{1}
      (ForgetEnrichment.to (Complex A) (dgCoherentBarGraded A PUnit.{1} (smallStrictBarDiagram A F)))
      (smallStrictBarTotalTarget A F)).d 0 1 (smallStrictBarTotalGradedElement A F) =
    compose A (D := RightModule A PUnit.{1}) (smallStrictBarTotalGradedElement A F)
      (dgCoherentBarTheta A PUnit.{1} (smallStrictBarDiagram A F)) (add_zero 1) := by
  let G := smallStrictBarDiagram A F
  let B := dgCoherentBarGraded A PUnit.{1} G
  let T := ForgetEnrichment.of (Complex A) (smallStrictBarTotalTarget A F)
  apply (dgCoherentBarHomEquiv A PUnit.{1} G T 1).injective
  funext s
  rw [dgCoherentBarHomEquiv_apply, dgCoherentBarHomEquiv_apply]
  let e := eHomWhiskerRight (Complex A) (Sigma.ι (dgCoherentBarFamily A PUnit.{1} G) s) T
  have hd := ConcreteCategory.congr_hom (e.comm 0 1).symm (smallStrictBarTotalGradedElement A F)
  apply hd.trans
  have hr := smallStrictBarTotalGradedElement_restrict A F s
  have h₁ := congrArg
    ((moduleHom A PUnit.{1} (ForgetEnrichment.to (Complex A) (dgCoherentBarFamily A PUnit.{1} G s))
      (smallStrictBarTotalTarget A F)).d 0 1) hr
  apply h₁.trans
  apply (smallStrictBarTotalColumn_d A F s).trans
  symm
  exact (moduleHomRestriction_compose A PUnit.{1}
    (S := dgCoherentBarFamily A PUnit.{1} G s) (M := B) (N := B) (P := T)
    (Sigma.ι (dgCoherentBarFamily A PUnit.{1} G) s)
    (dgCoherentBarTheta A PUnit.{1} G) (smallStrictBarTotalGradedElement A F) (add_zero 1)).trans
      (congrArg (fun z => compose A (D := RightModule A PUnit.{1})
        (smallStrictBarTotalGradedElement A F) z (add_zero 1))
        (dgCoherentBarTheta_restrict A PUnit.{1} G s))

/-- 元の実 MC bar へ戻した指定要素は閉じている。 -/
theorem smallStrictBarTotalElement_closed (F : J ⥤ ModuleCategory A PUnit.{1}) :
    (moduleHom A PUnit.{1}
      (dgCoherentBarModuleUnconditional A PUnit.{1} (smallStrictBarDiagram A F))
      (smallStrictBarTotalTarget A F)).d 0 1 (smallStrictBarTotalElement A F) = 0 := by
  apply (dgCoherentBarHomDegreeEquiv A PUnit.{1} (smallStrictBarDiagram A F)
    (dgCoherentBarMaurerCartan_unconditional A PUnit.{1} (smallStrictBarDiagram A F))
    (smallStrictBarTotalTarget A F) 1).injective
  rw [map_zero]
  have hd := dgCoherentBarHomDegreeEquiv_d A PUnit.{1} (smallStrictBarDiagram A F)
    (dgCoherentBarMaurerCartan_unconditional A PUnit.{1} (smallStrictBarDiagram A F))
    (smallStrictBarTotalTarget A F) 0 (smallStrictBarTotalElement A F)
  apply hd.trans
  rw [smallStrictBarTotalElement_graded A F]
  erw [smallStrictBarTotalGradedElement_d A F]
  simp

/-- 同じ閉要素が定める、元の実 bar から指定した全複体への厳密な射。 -/
def smallStrictBarTotalHom (F : J ⥤ ModuleCategory A PUnit.{1}) :
    ForgetEnrichment.of (Complex A)
      (dgCoherentBarModuleUnconditional A PUnit.{1} (smallStrictBarDiagram A F)) ⟶
    ForgetEnrichment.of (Complex A) (smallStrictBarTotalTarget A F) :=
  (closedHomEquiv A (RightModule A PUnit.{1}) _ _).symm
    ⟨smallStrictBarTotalElement A F, smallStrictBarTotalElement_closed A F⟩

/-- この厳密な射の閉零要素は、最初に指定した同じ比較要素そのもの。 -/
theorem smallStrictBarTotalHom_val (F : J ⥤ ModuleCategory A PUnit.{1}) :
    ((closedHomEquiv A (RightModule A PUnit.{1}) _ _) (smallStrictBarTotalHom A F)).val =
      smallStrictBarTotalElement A F :=
  congrArg Subtype.val ((closedHomEquiv A (RightModule A PUnit.{1}) _ _).apply_symm_apply _)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
