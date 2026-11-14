module

public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarTotalValues
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison
import all SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarTotalColumns
import all SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarTotalValues

/-!
# 元の bar の各因子への制限と後合成

## 概要
同じ graded 比較を各因子へ制限し、任意のブロックとの後合成の一点評価を計算する。

## 方針
既存の余積の全 Hom 同値と、評価での合成・左右 whisker の公式を使う。

## 規約
比較の閉性は仮定せず、元の同じ次数零要素で等式を述べる。

## 使われ方
HA 1.2.4。既存 theta の同じ列との合成の計算。
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
variable (F : J ⥤ ModuleCategory A PUnit.{1})

/-- 元の余積因子に制限すると、指定した同じ列を返す。 -/
theorem smallStrictBarTotalGradedElement_restrict
    (s : dgCoherentBarIndex ((SSet.uliftFunctor.{u, 0}).obj (nerve J))) :
    (eHomWhiskerRight (Complex A) (Sigma.ι (dgCoherentBarFamily A PUnit.{1} (smallStrictBarDiagram A F)) s) (ForgetEnrichment.of (Complex A) (smallStrictBarTotalTarget A F))).f 0 (smallStrictBarTotalGradedElement A F) =
      smallStrictBarTotalColumn A F s :=
  (dgCoherentBarHomEquiv_apply A PUnit.{1} (smallStrictBarDiagram A F)
    (ForgetEnrichment.of (Complex A) (smallStrictBarTotalTarget A F)) 0 (smallStrictBarTotalGradedElement A F) s).symm.trans
      (smallStrictBarTotalGradedElement_column A F s)

/-- 同じ制限の一点評価は、元の包含の後の同じ graded 比較の合成。 -/
theorem smallStrictBarTotalColumn_point_restrict
    (s : dgCoherentBarIndex ((SSet.uliftFunctor.{u, 0}).obj (nerve J))) :
    (moduleHomπ A PUnit.{1} (ForgetEnrichment.to (Complex A) ((dgCoherentBarFamily A PUnit.{1} (smallStrictBarDiagram A F)) s)) (smallStrictBarTotalTarget A F) PUnit.unit).f 0
        (smallStrictBarTotalColumn A F s) =
      (Cochain.ofHom ((moduleEvaluation A PUnit.{1} PUnit.unit).map (Sigma.ι (dgCoherentBarFamily A PUnit.{1} (smallStrictBarDiagram A F)) s))).comp
        ((moduleHomπ A PUnit.{1} (ForgetEnrichment.to (Complex A) (dgCoherentBarGraded A PUnit.{1} (smallStrictBarDiagram A F))) (smallStrictBarTotalTarget A F) PUnit.unit).f 0 (smallStrictBarTotalGradedElement A F))
        (zero_add 0) :=
  (congrArg (fun z =>
    (moduleHomπ A PUnit.{1} (ForgetEnrichment.to (Complex A) ((dgCoherentBarFamily A PUnit.{1} (smallStrictBarDiagram A F)) s)) (smallStrictBarTotalTarget A F) PUnit.unit).f 0 z)
    (smallStrictBarTotalGradedElement_restrict A F s)).symm.trans
      (moduleHomWhiskerRight_apply_π A PUnit.{1} (Sigma.ι (dgCoherentBarFamily A PUnit.{1} (smallStrictBarDiagram A F)) s) 0 (smallStrictBarTotalGradedElement A F) PUnit.unit)

/-- 各因子への任意の同じブロックを後合成したときの、指定列による評価公式。 -/
theorem smallStrictBarTotalGradedElement_postBlock
    (s : dgCoherentBarIndex ((SSet.uliftFunctor.{u, 0}).obj (nerve J)))
    (M : ModuleCategory A PUnit.{1}) (k : ℤ)
    (b : (moduleHom A PUnit.{1} (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) ((dgCoherentBarFamily A PUnit.{1} (smallStrictBarDiagram A F)) s))).X k) :
    (moduleHomπ A PUnit.{1} (ForgetEnrichment.to (Complex A) M) (smallStrictBarTotalTarget A F) PUnit.unit).f k
        (compose A (smallStrictBarTotalGradedElement A F) ((eHomWhiskerLeft (Complex A) M (Sigma.ι (dgCoherentBarFamily A PUnit.{1} (smallStrictBarDiagram A F)) s)).f k b) (add_zero k)) =
      ((moduleHomπ A PUnit.{1} (ForgetEnrichment.to (Complex A) M)
        (ForgetEnrichment.to (Complex A) ((dgCoherentBarFamily A PUnit.{1} (smallStrictBarDiagram A F)) s)) PUnit.unit).f k b).comp
        ((moduleHomπ A PUnit.{1} (ForgetEnrichment.to (Complex A) ((dgCoherentBarFamily A PUnit.{1} (smallStrictBarDiagram A F)) s)) (smallStrictBarTotalTarget A F) PUnit.unit).f 0
          (smallStrictBarTotalColumn A F s)) (add_zero k) := by
  let B := dgCoherentBarFamily A PUnit.{1} (smallStrictBarDiagram A F)
  let P := dgCoherentBarGraded A PUnit.{1} (smallStrictBarDiagram A F)
  let ι : B s ⟶ P := Sigma.ι B s
  let c := (moduleHomπ A PUnit.{1} (ForgetEnrichment.to (Complex A) P)
    (smallStrictBarTotalTarget A F) PUnit.unit).f 0 (smallStrictBarTotalGradedElement A F)
  let v := (moduleHomπ A PUnit.{1} (ForgetEnrichment.to (Complex A) M)
    (ForgetEnrichment.to (Complex A) (B s)) PUnit.unit).f k b
  have hp := moduleHomWhiskerLeft_apply_π A PUnit.{1} ι k b PUnit.unit
  exact (moduleHomCompose_π A PUnit.{1} (smallStrictBarTotalGradedElement A F)
      ((eHomWhiskerLeft (Complex A) M ι).f k b) (add_zero k) PUnit.unit).trans
    ((congrArg (fun z => z.comp c (add_zero k)) hp).trans
      ((Cochain.comp_assoc_of_second_is_zero_cochain v
        (Cochain.ofHom ((moduleEvaluation A PUnit.{1} PUnit.unit).map ι)) c (add_zero k)).trans
          (congrArg (fun z => v.comp z (add_zero k))
            (smallStrictBarTotalColumn_point_restrict A F s).symm)))

/-- 同じ graded 要素を、元の Maurer–Cartan bar からの次数零の要素へ戻す。 -/
def smallStrictBarTotalElement :
    (moduleHom A PUnit.{1}
      (dgCoherentBarModuleUnconditional A PUnit.{1} (smallStrictBarDiagram A F))
      (smallStrictBarTotalTarget A F)).X 0 :=
  (dgCoherentBarHomDegreeEquiv A PUnit.{1} (smallStrictBarDiagram A F)
    (dgCoherentBarMaurerCartan_unconditional A PUnit.{1} (smallStrictBarDiagram A F))
    (smallStrictBarTotalTarget A F) 0).symm (smallStrictBarTotalGradedElement A F)

/-- 元の bar の要素を graded Hom へ戻すと、同じ指定要素そのもの。 -/
theorem smallStrictBarTotalElement_graded :
    dgCoherentBarHomDegreeEquiv A PUnit.{1} (smallStrictBarDiagram A F)
      (dgCoherentBarMaurerCartan_unconditional A PUnit.{1} (smallStrictBarDiagram A F))
      (smallStrictBarTotalTarget A F) 0 (smallStrictBarTotalElement A F) =
        smallStrictBarTotalGradedElement A F :=
  (dgCoherentBarHomDegreeEquiv A PUnit.{1} (smallStrictBarDiagram A F)
    (dgCoherentBarMaurerCartan_unconditional A PUnit.{1} (smallStrictBarDiagram A F))
    (smallStrictBarTotalTarget A F) 0).apply_symm_apply _

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
