module

public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarTotalClosed
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarDegreeCofan
import all SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarTotalComposition
import all SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.HomDegrees

/-!
# 元の厳密な比較射の各次数の成分

## 概要
閉零要素から戻した射の一点評価と、同じ graded 比較の各成分を同定する。

## 方針
閉零射と cycle の逆則、MC の Hom 次数同値の成分公式を用いる。

## 規約
MC bar と graded bar の同じ各次数の台を保つ。

## 使われ方
HA 1.2.4。比較射が同じ余積同型の前向きの射であることの確認。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open HomologicalComplex CochainComplex HomComplex SerrePositivity.DifferentialGraded
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
variable (A : Type u) [CommRing A] {J : Type} [SmallCategory J]

/-- 同じ厳密な射の一点評価は、元の graded 比較と同じ成分を持つ。 -/
theorem smallStrictBarTotalHom_point_f (F : J ⥤ ModuleCategory A PUnit.{1}) (q : ℤ) :
    ((moduleEvaluation A PUnit.{1} PUnit.unit).map (smallStrictBarTotalHom A F)).f q =
      ((moduleHomπ A PUnit.{1}
        (ForgetEnrichment.to (Complex A) (dgCoherentBarGraded A PUnit.{1} (smallStrictBarDiagram A F)))
        (smallStrictBarTotalTarget A F) PUnit.unit).f 0 (smallStrictBarTotalGradedElement A F)).v
        q q (add_zero q) := by
  change ((moduleHomπ A PUnit.{1}
    (dgCoherentBarModuleUnconditional A PUnit.{1} (smallStrictBarDiagram A F))
    (smallStrictBarTotalTarget A F) PUnit.unit).f 0
    (((closedHomEquiv A (RightModule A PUnit.{1}) _ _) (smallStrictBarTotalHom A F)).val)).v
      q q (add_zero q) = _
  rw [smallStrictBarTotalHom_val A F]
  have h := dgCoherentBarHomDegreeEquiv_π A PUnit.{1} (smallStrictBarDiagram A F)
    (dgCoherentBarMaurerCartan_unconditional A PUnit.{1} (smallStrictBarDiagram A F))
    (smallStrictBarTotalTarget A F) 0 (smallStrictBarTotalElement A F) PUnit.unit q q (add_zero q)
  rw [smallStrictBarTotalElement_graded A F] at h
  exact h.symm

/-- 元の射列の各因子への制限は、同じ指定比較列の成分。 -/
theorem smallStrictBarTotalHom_point_ι (F : J ⥤ ModuleCategory A PUnit.{1}) (q : ℤ)
    (s : dgCoherentBarIndex ((SSet.uliftFunctor.{u, 0}).obj (nerve J))) :
    ((moduleEvaluation A PUnit.{1} PUnit.unit).map
      (Sigma.ι (dgCoherentBarFamily A PUnit.{1} (smallStrictBarDiagram A F)) s)).f q ≫
        ((moduleEvaluation A PUnit.{1} PUnit.unit).map (smallStrictBarTotalHom A F)).f q =
      (smallStrictBarDegreeCofan A F q).inj s := by
  rw [smallStrictBarTotalHom_point_f A F q]
  have h := congrArg (fun z => z.v q q (add_zero q))
    (smallStrictBarTotalColumn_point_restrict A F s)
  rw [Cochain.comp_v _ _ _ q q q (add_zero q) (add_zero q)] at h
  exact h.symm

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
