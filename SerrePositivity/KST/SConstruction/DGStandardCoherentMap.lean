module
public import SerrePositivity.KST.SConstruction.DGStandardEnrichedFunctor
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.NervePostcomposition

/-! # 厳密 dg 関手の標準 DK coherent nerve 上の作用
概要：標準 DK の厳密豊穣関手へ γ1 を適用し、元の dg 関手の ∞ 関手を得る。
方針：既存の coherent nerve の関手性に単位・合成の厳密な保存を渡す。
規約：対象の宇宙を共通に取り、元の DK Hom を保持する。使われ方：dg 関手圏の core。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

open scoped Simplicial
variable {A : Type u} [CommRing A] {D E B : Type v}
  [DGCategory A D] [DGCategory A E] [DGCategory A B]

/-- 元の厳密 dg 関手による、標準 DK coherent nerve の ∞ 関手。 -/
def dgStandardCoherentMap (F : DGFunctor A D E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanCoherentNerve (R := A) (D := D) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanCoherentNerve (R := A) (D := E) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (dgStandardEnrichedFunctor F)

/-- γ1 で得た標準 DK ∞ 関手は、元の恒等関手を保存する。 -/
lemma dgStandardCoherentMap_id :
    dgStandardCoherentMap (DGFunctor.id (A := A) D) =
      𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanCoherentNerve (R := A) (D := D)) := by
  rw [dgStandardCoherentMap, dgStandardEnrichedFunctor_id, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_id]
  rfl

/-- γ1 で得た標準 DK ∞ 関手は、元の dg 合成を保存する。 -/
lemma dgStandardCoherentMap_comp (F : DGFunctor A D E) (G : DGFunctor A E B) :
    dgStandardCoherentMap (F.comp G) = dgStandardCoherentMap F ≫ dgStandardCoherentMap G := by
  rw [dgStandardCoherentMap, dgStandardEnrichedFunctor_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp]
  rfl

/-- γ1 による作用は、元の対象の標準頂点の像を回収する。 -/
lemma dgStandardCoherentMap_vertex (F : DGFunctor A D E) (x : ClosedCategory A D) :
    (dgStandardCoherentMap F).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (ForgetEnrichment.of (Complex A) (F.obj x)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex (dgStandardEnrichedFunctor F) x

end SerrePositivity.KST.SConstruction
