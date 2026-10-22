module

public import SerrePositivity.InfinityCategories.F2.Ind.SectionProductCoefficientFiberIso
public import SerrePositivity.InfinityCategories.F2.Ind.SectionProductValueEquivalence
public import SerrePositivity.InfinityCategories.F1.LeftScaffoldComparison

/-!
概要：全単体の切断から同じ初頂点引き戻しへの大域評価自体は前合成同値。
方針：元の fiber 比較を同じ初頂点評価と元の fiber 同型へ同定し、既存の scaffold 判定を使う。
規約：底の quasicategory 性も replacement の充填性も追加しない。
使われ方：共同 weighted 分類と strict 分類像の全単体上の大域比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
attribute [local instance] vertexFiber_kanComplex_of_leftFibration
variable {I : Type u} [Category.{u} I] {B : SSet.{u}} (F : I ⥤ LeftFibrationObject B)

/-- 元の大域射の係数から fiber への作用は、同じ初頂点評価と同じ fiber 同型の合成。 -/
lemma sectionProductScaffold_fiber (i : I) (s : TransportSimplexCategory B) :
    leftScaffoldFiberMap
      (pullback.snd (leftFibrationWeightedProjection F) (sectionProductBaseMap I B))
      (strictLeftTransportSectionDiagram F ⋙ kanObjectForget) (sectionProductScaffold F)
      (sectionProductScaffold_projection F) (i, s) =
        sectionProductValueEvaluation F i s ≫ (sectionProductCoefficientFiberIso F i s).hom := by
  apply vertexFiber_hom_ext
  change simplicialReplacementConstantLift
    (strictLeftTransportSectionDiagram F ⋙ kanObjectForget) (i, s) ≫ sectionProductScaffold F =
      (sectionProductValueEvaluation F i s ≫ (sectionProductCoefficientFiberIso F i s).hom) ≫ _
  apply pullback.hom_ext
  · simp only [Category.assoc]
    rw [sectionProductScaffold_total, sectionProductWeightedEvaluation_value,
      sectionProductCoefficientFiberIso_total]
  · simp only [Category.assoc]
    rw [sectionProductScaffold_projection, simplicialReplacementConstantLift_projection,
      vertexFiberι_comp, SSet.comp_const, SSet.comp_const]

/-- 同じ大域射は、全ての元の係数値で fiber 同値を誘導する left scaffold。 -/
lemma sectionProductScaffold_isLeftScaffold :
    IsLeftScaffold
      (pullback.snd (leftFibrationWeightedProjection F) (sectionProductBaseMap I B))
      (strictLeftTransportSectionDiagram F ⋙ kanObjectForget) (sectionProductScaffold F) := by
  refine ⟨sectionProductScaffold_projection F, ?_⟩
  rintro ⟨i, s⟩
  rw [sectionProductScaffold_fiber]
  exact (sectionProductValueEvaluation_isQCatEquivalence F i s).comp
    (qCatEquivalenceOfIso (sectionProductCoefficientFiberIso F i s)).isQCatEquivalence

/-- 元の全切断の大域評価射そのものは前合成同値。 -/
lemma sectionProductScaffold_isPrecompositionEquivalence :
    IsPrecompositionEquivalence (sectionProductScaffold F) :=
  (sectionProductScaffold_isLeftScaffold F).isPrecompositionEquivalence

end SerrePositivity.InfinityCategories.F2.Ind
