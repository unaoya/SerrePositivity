module
public import SerrePositivity.InfinityCategories.Derived.KappaCovers.PartialTower

/-!
概要：κ-small な依存閉部分 cell 加群が、標準 resolution の全要素を覆う。
方針：元を有限段へ戻し、有限 support の依存閉包を取って小さい前段へ持ち上げる。
規約：これは実 strict 加群の次数ごとの網羅性である。
使われ方：D-8 d の κ-filtered strict 余極限表示。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (M : ModuleCategory R D) {κ : Cardinal.{u}} [Fact κ.IsRegular]
  (hκ : Cardinal.aleph0 < κ)
include hκ

lemma dgKappaResolutionPieces_coverFinite (t : Finset (DGKappaResolutionLabel R D M)) :
    ∃ s : DGKappaResolutionPieces R D M κ, (↑t : Set _) ⊆ s.val := by
  classical
  have ht : HasCardinalLT (↑t : Set (DGKappaResolutionLabel R D M)) κ :=
    hasCardinalLT_of_finite _ _ hκ.le
  let dep := dgKappaResolutionDependencies R D M
  refine ⟨⟨dgKappaDependencyClosure dep ↑t,
    dgKappaDependencyClosure_small dep hκ (dgKappaResolutionDependencies_small R D M hκ) ht,
    fun _ ha => dgKappaDependencyClosure_closed dep ↑t ha⟩,
    dgKappaDependencyClosure_contains dep ↑t⟩

lemma dgKappaPartialResolution_jointlySurjective (x : D) (q : ℤ)
    (z : ((moduleEvaluation R D x).obj (moduleResolutionCandidate R D M)).X q) :
    ∃ s : DGKappaResolutionPieces R D M κ,
      ∃ b : ((moduleEvaluation R D x).obj
        (dgKappaPartialResolution R D M s.val s.property.2)).X q,
        ((moduleEvaluation R D x).map
          (dgKappaPartialResolutionInclusion R D M s.val s.property.2)).f q b = z := by
  obtain ⟨n, a, ha⟩ := moduleResolutionCandidate_element_rep R D M x q z
  obtain ⟨s, hs⟩ := dgKappaResolutionPieces_coverFinite R D M hκ
    (dgKappaResolutionElementSupport R D M n x q a)
  let p := dgKappaResolutionPartialStage R D M s.val s.property.2 n
  obtain ⟨b, hb⟩ := p.supported x q a (dgKappaResolutionElementSupport_spec R D M n x q a hs)
  refine ⟨s, ((moduleEvaluation R D x).map
    (colimit.ι (dgKappaPartialResolutionDiagram R D M s.val s.property.2) n)).f q b, ?_⟩
  have hf := congrArg (fun f => ((moduleEvaluation R D x).map f).f q b)
    (colimit.ι_desc (dgKappaPartialResolutionCocone R D M s.val s.property.2) n)
  have hr := congrArg (((moduleEvaluation R D x).map (moduleResolutionCandidateι R D M n)).f q) hb
  have hf' : ((moduleEvaluation R D x).map
      (dgKappaPartialResolutionInclusion R D M s.val s.property.2)).f q
        (((moduleEvaluation R D x).map
          (colimit.ι (dgKappaPartialResolutionDiagram R D M s.val s.property.2) n)).f q b) =
      ((moduleEvaluation R D x).map (moduleResolutionCandidateι R D M n)).f q
        (((moduleEvaluation R D x).map p.inclusion).f q b) := by
    simpa only [dgKappaPartialResolutionCocone, NatTrans.ofSequence_app,
      CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f,
      ModuleCat.comp_apply] using! hf
  exact hf'.trans (hr.trans ha)

end SerrePositivity.InfinityCategories
