module
public import SerrePositivity.InfinityCategories.Derived.DGVerdierRightKanLimits
public import SerrePositivity.InfinityCategories.Derived.CosliceRealizationLimitCone
public import SerrePositivity.InfinityCategories.Derived.RightKanPrecompositionFaithful
public import SerrePositivity.InfinityCategories.F1B.KanRightCanonicalMapping
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]
/-- 商像の各元の対象で、任意後合成の標準右 Kan 錐は実極限錐。 -/
lemma dgVerdierRightKanCanonicalCone_isLimit (P : Set D) (hP : DGQuotient.localKFlat A D P)
    (x : D) {Y : SSet.{max u v}} [Quasicategory Y] (G : dgQuotientNerve A D P ⟶ Y) :
    IsLimitCone (rightKanCanonicalCone (dgQuotientNerveProjection A D P) G
      (Simplex.vertex ((DGQuotient.inclusion A D P).obj x))) := by
  obtain ⟨R⟩ := dgVerdierRightKanDiagram_nonempty A D P hP x
  apply (isLimitCone_iff_restrict_of_leftCofinal (dgVerdierRightKanMap A D P hP x R)
    (dgVerdierRightKanMap_isLeftCofinal A D P hP x R) _ _).mpr
  let c := F2.restrictJoinCone (rightKanCanonicalCone (dgQuotientNerveProjection A D P) G
    (Simplex.vertex ((DGQuotient.inclusion A D P).obj x))) (dgVerdierRightKanMap A D P hP x R)
  have hd : IsLimitCone (R.postcompCone G) := by
    apply CosliceHomotopyRealization.postcompCone_isLimit R _
      (dgVerdierOver_isWeaklyContractible A D P x) G
    intro a
    exact simplicialHomotopyOfFunctorEdge_vertex_isInvertible
      (FunctorIso.edge (dgVerdierOverQuotientEvaluationIso A D P hP x).symm)
      (FunctorIso.edge_isInvertible (dgVerdierOverQuotientEvaluationIso A D P hP x).symm) a
  have he : c.val = (R.postcompCone G).val := by
    change joinMap (𝟙 (Δ[0] : SSet.{max u v})) (dgVerdierRightKanMap A D P hP x R) ≫
      (sliceUnderUncurry (pullback.fst _ _) ≫ G) = sliceUnderUncurry R.diagram ≫ G
    rw [← Category.assoc, ← sliceUnderUncurry_precomp, dgVerdierRightKanMap_coslice]
  have ei : FunctorIso (R.postcompCone G).val c.val :=
    eqToIso (congrArg (fun t => SSet.HomotopyCategory.mk (functorVertex t)) he.symm)
  exact IsLimitCone.of_functorIso hd ei
/-- 商の全頂点で、任意後合成の標準右 Kan 錐は実極限錐。 -/
lemma dgVerdierRightKanCanonicalCone_isLimit_all (P : Set D)
    (hP : DGQuotient.localKFlat A D P) {Y : SSet.{max u v}} [Quasicategory Y]
    (G : dgQuotientNerve A D P ⟶ Y) (z : (dgQuotientNerve A D P) _⦋0⦌) :
    IsLimitCone (rightKanCanonicalCone (dgQuotientNerveProjection A D P) G z) := by
  let x := (dgNerve.vertexEquiv A (DGQuotient.QuotientObject D P)) z
  have hz : Simplex.vertex x = z := (dgNerve.vertexEquiv A _).symm_apply_apply z
  have h := dgVerdierRightKanCanonicalCone_isLimit A D P hP x.val G
  exact (congrArg (fun t => IsLimitCone
    (rightKanCanonicalCone (dgQuotientNerveProjection A D P) G t)) hz).mp h
/-- 商上の任意関手は、商への制限と実恒等変換に関する実右 Kan 拡張。 -/
lemma dgVerdierRightKanExtension_refl (P : Set D) (hP : DGQuotient.localKFlat A D P)
    {Y : SSet.{max u v}} [Quasicategory Y] (G : dgQuotientNerve A D P ⟶ Y) :
    IsRightKanExtension (dgQuotientNerveProjection A D P)
      (dgQuotientNerveProjection A D P ≫ G) G
      (functorHomotopyRefl (dgQuotientNerveProjection A D P ≫ G)) :=
  F1B.kanRightKanExtension_refl_of_canonicalLimits (dgQuotientNerveProjection A D P) G
    (dgVerdierRightKanCanonicalCone_isLimit_all A D P hP G)
/-- 商関手の前合成は、任意標的の全反転関手圏で充満忠実。 -/
lemma dgVerdierLocalizationPrecomposition_isFullyFaithful (P : Set D)
    (hP : DGQuotient.localKFlat A D P) (Y : SSet.{max u v}) [Quasicategory Y] :
    IsFullyFaithful (localizationPrecomposition (dgQuotientNerveProjection A D P)
      (dgVerdierEdges A D P) (dgQuotientNerveProjection_invertsVerdierEdges A D P hP) Y) :=
  localizationPrecomposition_isFullyFaithful_of_rightKan _ _ _
    (fun _ _ => dgVerdierRightKanExtension_refl A D P hP) Y
end SerrePositivity.InfinityCategories
