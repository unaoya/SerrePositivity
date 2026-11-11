module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierRightKanLimits
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CosliceRealizationLimitCone
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightPrecompositionFaithful
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightCanonicalMapping
/-!
概要：商上の任意関手は、商関手での制限からの実右 Kan 拡張である。
方針：実逆分母への cofinal 制限後の標準錐を、全 prism を持つ coslice 実現の実極限錐と同定する。
規約：任意 quasicategory 標的。使われ方：商関手の前合成の全関手圏での充満忠実性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
/-- 商像の各元の対象で、任意後合成の標準右 Kan 錐は実極限錐。 -/
lemma dgVerdierRightKanCanonicalCone_isLimit (P : Set D) (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P)
    (x : D) {Y : SSet.{max u v}} [Quasicategory Y] (G : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve A D P ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanCanonicalCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P) G
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((DGQuotient.inclusion A D P).obj x))) := by
  obtain ⟨R⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierRightKanDiagram_nonempty A D P hP x
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isLimitCone_iff_restrict_of_leftCofinal (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierRightKanMap A D P hP x R)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierRightKanMap_isLeftCofinal A D P hP x R) _ _).mpr
  let c := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanCanonicalCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P) G
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((DGQuotient.inclusion A D P).obj x))) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierRightKanMap A D P hP x R)
  have hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (R.postcompCone G) := by
    apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.CosliceHomotopyRealization.postcompCone_isLimit R _
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver_isWeaklyContractible A D P x) G
    intro a
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.simplicialHomotopyOfFunctorEdge_vertex_isInvertible
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.edge (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverQuotientEvaluationIso A D P hP x).symm)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.edge_isInvertible (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverQuotientEvaluationIso A D P hP x).symm) a
  have he : c.val = (R.postcompCone G).val := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{max u v})) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierRightKanMap A D P hP x R) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry (pullback.fst _ _) ≫ G) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry R.diagram ≫ G
    rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierRightKanMap_coslice]
  have ei : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (R.postcompCone G).val c.val :=
    eqToIso (congrArg (fun t => SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex t)) he.symm)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone.of_functorIso hd ei
/-- 商の全頂点で、任意後合成の標準右 Kan 錐は実極限錐。 -/
lemma dgVerdierRightKanCanonicalCone_isLimit_all (P : Set D)
    (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P) {Y : SSet.{max u v}} [Quasicategory Y]
    (G : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve A D P ⟶ Y) (z : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve A D P) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanCanonicalCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P) G z) := by
  let x := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (DGQuotient.QuotientObject D P)) z
  have hz : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x = z := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A _).symm_apply_apply z
  have h := dgVerdierRightKanCanonicalCone_isLimit A D P hP x.val G
  exact (congrArg (fun t => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanCanonicalCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P) G t)) hz).mp h
/-- 商上の任意関手は、商への制限と実恒等変換に関する実右 Kan 拡張。 -/
lemma dgVerdierRightKanExtension_refl (P : Set D) (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P)
    {Y : SSet.{max u v}} [Quasicategory Y] (G : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve A D P ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRightKanExtension (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P ≫ G) G
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P ≫ G)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRightKanExtension_refl_of_canonicalLimits (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P) G
    (dgVerdierRightKanCanonicalCone_isLimit_all A D P hP G)
/-- 商関手の前合成は、任意標的の全反転関手圏で充満忠実。 -/
lemma dgVerdierLocalizationPrecomposition_isFullyFaithful (P : Set D)
    (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P) (Y : SSet.{max u v}) [Quasicategory Y] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection_invertsVerdierEdges A D P hP) Y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.localizationPrecomposition_isFullyFaithful_of_rightKan _ _ _
    (fun _ _ => dgVerdierRightKanExtension_refl A D P hP) Y
end SerrePositivity.InfinityCategories.Project.DerivedCategories
