module

public import SerrePositivity.KST.Spectra.D3ProjectionStructureIso

/-!
概要：元の BF 構造同型は、nativeTail への前合成で同じ次段構造同型を回収する。
方針：同じ構造随伴射の段移動を厳密豊穣変換で照合し、指定区間族の前合成へ移す。
規約：円交換因子を比較しない。指定同型の値と全 Hom の自然性を保持する。
使われ方：実段 loop 図式の厳密 tail 終点と右射影の構造正方形の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
local instance d3StructureTailSpectrumCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 同じ次段通常 loop の全豊穣作用も、元の tail と厳密に可換。 -/
lemma d3StageLoopTail_enriched (n : ℕ) :
    tailEnriched.comp SSet (d3StageLoopKanEnriched.{u} n) =
      d3StageLoopKanEnriched (n + 1) := by
  rw [d3StageLoopKanEnriched, ← d3EnrichedComp_assoc, d3StageTail_enriched]
  rfl

/-- 元の同じ構造変換へ tail を前合成し、同じ次段端点へ正規化する。 -/
def d3StageStructureTailGraded (n : ℕ) :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u}))
      (d3StageKanEnriched (n + 1)) (d3StageLoopKanEnriched (n + 1)) :=
  d3GradedOfEq (d3GradedPrecomp tailEnriched (d3StageStructureGraded n))
    (d3StageTail_enriched n) (d3StageLoopTail_enriched n)

/-- 指定構造変換の tail 像は、元の次段構造変換そのもの。 -/
lemma d3StageStructureTailGraded_eq (n : ℕ) :
    d3StageStructureTailGraded.{u} n = d3StageStructureGraded (n + 1) := by
  apply d3Graded_ext
  intro X
  have h := d3GradedOfEq_component_heq
    (d3GradedPrecomp tailEnriched (d3StageStructureGraded n))
    (d3StageTail_enriched n) (d3StageLoopTail_enriched n) X
  apply eq_of_heq
  apply h.trans
  change HEq (StrictEnrichedTransformation.componentHom _ _ (d3StageStructureGraded n) (tail X)) _
  rw [d3StageStructureGraded_component, d3StageStructureGraded_component]
  rfl

/-- 既存の同じ構造同型の tail 前合成の、元の次段端点での表示。 -/
def d3StageStructureTailFunctorIso (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3StageKanEnriched.{u} (n + 1)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3StageKanEnriched (n + 2)) ≫ pointedKanLoopInfinity) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq ((d3StageStructureFunctorIso n).precomp nativeTail)
    (d3StageTail n) (by rw [← Category.assoc, d3StageTail])

private lemma d3StructureTailGraded_inv (n : ℕ) (X : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (StrictEnrichedTransformation.componentHom _ _
      (d3StageStructureGraded n) X)).toTruncated := by
  rw [d3StageStructureGraded_component]
  exact pointedKanObject_edge_isInvertible_of_piIsomorphism _
    (KanSequence.adjointLoopTailUnit_levelwise X.toKanSequence_omega n)

/-- 指定構造同型への同じ tail 前合成の順射は、元の次段厳密変換の実現値。 -/
lemma d3StageStructureTailFunctorIso_hom_heq (n : ℕ) :
    HEq (d3StageStructureTailFunctorIso.{u} n).hom
      (d3GradedHom (d3StageStructureGraded (n + 1))) := by
  unfold d3StageStructureTailFunctorIso
  apply HEq.trans (d3FunctorIsoOfEq_hom_heq _ _ _)
  unfold d3StageStructureFunctorIso
  apply HEq.trans (d3FunctorIsoOfEq_precomp_hom_heq _ _ _ _)
  have h := d3GradedIso_precomp_hom_heq tailEnriched (d3StageStructureGraded n)
    (d3StructureTailGraded_inv n)
  have ht := d3GradedHom_ofEq_heq (d3GradedPrecomp tailEnriched (d3StageStructureGraded n))
    (d3StageTail_enriched n) (d3StageLoopTail_enriched n)
  have ht' : d3GradedHom (d3StageStructureTailGraded n) =
      d3GradedHom (d3StageStructureGraded (n + 1)) := by rw [d3StageStructureTailGraded_eq]
  exact h.trans (ht.symm.trans (heq_of_eq ht'))

/-- 元の BF 構造同型は、厳密 tail 前合成で元の同じ次段構造同型を回収する。 -/
lemma d3StageStructureTailFunctorIso_eq (n : ℕ) :
    d3StageStructureTailFunctorIso.{u} n = d3StageStructureFunctorIso (n + 1) := by
  apply Iso.ext
  have h : HEq (d3StageStructureFunctorIso (n + 1)).hom
      (d3GradedHom (d3StageStructureGraded (n + 1))) := by
    unfold d3StageStructureFunctorIso
    exact d3FunctorIsoOfEq_hom_heq _ _ _
  exact eq_of_heq ((d3StageStructureTailFunctorIso_hom_heq n).trans h.symm)

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
