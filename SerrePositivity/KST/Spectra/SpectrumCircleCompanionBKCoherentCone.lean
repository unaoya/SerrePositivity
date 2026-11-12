module

public import SerrePositivity.KST.Spectra.SpectrumCircleCompanionReflectedTriangles
public import SerrePositivity.KST.Spectra.BousfieldKanPointSectionCoefficients
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.ReflectedStrictConeEvaluation

/-!
概要：元の companion の切断点から coherent 錐を復元し、その全切断を元の係数で計算する。
方針：固定頂点の全単射と反転 end の普遍評価を、点の初区間の係数へ戻す。
規約：既存の companion の切断点をそのまま使う。使われ方：元の評価錐全体との比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance companionBKCoherentConeSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory

/-- 元の companion の end の点を、同じ反転 end への単位パラメータの射として表す。 -/
def circleCompanionBKReflectedPointMap (z : Sp.{u} _⦋0⦌) :=
  circleCompanionBKEndPointMap z ≫
    circleCompanionBKReflection (nativeCotensorInput PointedSimplicialSet.circle z).val

/-- 元の反転点の全切断は、単位パラメータの普遍性から得る同じ全切断。 -/
lemma circleCompanionBKReflectedPointMap_transform (z : Sp.{u} _⦋0⦌) :
    BousfieldKanPointSection.transform (circleCompanionBKReflectedPointMap z) =
      circleCompanionBKReflectedSection z :=
  (circleCompanionBKReflectedSection_uncurry z).symm

/-- 元の切断点の Yoneda 表示は、同じ反転 end の元の点の比較像。 -/
lemma circleCompanionConeSectionPoint_yoneda (z : Sp.{u} _⦋0⦌) :
    SSet.yonedaEquiv.symm (circleCompanionConeSectionPoint z) =
      SSet.yonedaEquiv.symm (ULift.up
        (SSet.unitHomEquiv _ (circleCompanionBKReflectedPointMap z))) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedHomHolimConeComparison
          (pointLoopDiagram (nativeCotensorInput PointedSimplicialSet.circle z).val)
          (cotensor PointedSimplicialSet.circle
            (nativeCotensorInput PointedSimplicialSet.circle z).val) := by
  rw [circleCompanionConeSectionPoint, ← circleCompanionBKReflectedSection_point,
    ← SSet.yonedaEquiv_symm_comp]
  rfl

/-- 既存の companion の固定頂点の切断点を、そのまま元の図式上の全 coherent 錐へ戻す。 -/
def circleCompanionBKCoherentCone (z : Sp.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram
      (pointLoopDiagram (nativeCotensorInput PointedSimplicialSet.circle z).val)) :=
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.fixedVertexConeSpaceEquiv
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram
      (pointLoopDiagram (nativeCotensorInput PointedSimplicialSet.circle z).val))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (cotensor PointedSimplicialSet.circle
      (nativeCotensorInput PointedSimplicialSet.circle z).val))).symm
    (circleCompanionConeSectionPoint z)).val

/-- この元の companion の coherent 錐も、元の円 cotensor を頂点に持つ。 -/
lemma circleCompanionBKCoherentCone_vertex (z : Sp.{u} _⦋0⦌) :
    (circleCompanionBKCoherentCone z).vertex =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (cotensor PointedSimplicialSet.circle
        (nativeCotensorInput PointedSimplicialSet.circle z).val) := by
  have h := ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.fixedVertexConeSpaceEquiv
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram
      (pointLoopDiagram (nativeCotensorInput PointedSimplicialSet.circle z).val))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (cotensor PointedSimplicialSet.circle
      (nativeCotensorInput PointedSimplicialSet.circle z).val))).symm
    (circleCompanionConeSectionPoint z)).property
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.vertex_eq]
  exact (congrArg SSet.yonedaEquiv h).trans (Equiv.apply_symm_apply _ _)

/-- 元の companion 錐全体は、同じ点の元の weighted nerve 切断から厳密に復元できる。 -/
lemma circleCompanionBKCoherentCone_val (z : Sp.{u} _⦋0⦌) :
    (circleCompanionBKCoherentCone z).val =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry
        ((SSet.uliftFunctor.{u + 1, u}).map
          (BousfieldKanPointSection.sectionMap (circleCompanionBKReflectedPointMap z)) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCosliceComparison
            (pointLoopDiagram (nativeCotensorInput PointedSimplicialSet.circle z).val)
            (cotensor PointedSimplicialSet.circle
              (nativeCotensorInput PointedSimplicialSet.circle z).val)) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry (inv (fst _ (Δ[0] : SSet.{u + 1})) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (SSet.yonedaEquiv.symm (circleCompanionConeSectionPoint z))) = _
  apply congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry
  erw [circleCompanionConeSectionPoint_yoneda,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.relativeFunctorUncurry_parameter, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedHomHolimConeComparison_uncurry]
  have h := congrArg (fun f ↦ f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCosliceComparison
      (pointLoopDiagram (nativeCotensorInput PointedSimplicialSet.circle z).val)
      (cotensor PointedSimplicialSet.circle
        (nativeCotensorInput PointedSimplicialSet.circle z).val))
    (BousfieldKanPointSection.liftedSection.{u, u + 1} (circleCompanionBKReflectedPointMap z))
  simpa only [Category.assoc] using h

/-- 元の coherent 錐の各標準単体への制限は、同じ全切断の weighted cone simplex。 -/
lemma circleCompanionBKCoherentCone_simplex (z : Sp.{u} _⦋0⦌) {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} WalkingCospan) n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u + 1}))
      (SSet.yonedaEquiv.symm (ULift.up σ)) ≫ (circleCompanionBKCoherentCone z).val =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftPointStdSimplexIso n).hom ≫ SSet.yonedaEquiv.symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeSimplex
        (pointLoopDiagram (nativeCotensorInput PointedSimplicialSet.circle z).val)
        (cotensor PointedSimplicialSet.circle
          (nativeCotensorInput PointedSimplicialSet.circle z).val)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.prefixOverWeight σ ≫ Functor.whiskerLeft σ (circleCompanionBKReflectedSection z))) := by
  rw [circleCompanionBKCoherentCone_val, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_precomp]
  have hs : SSet.yonedaEquiv.symm (ULift.up σ) ≫
      (SSet.uliftFunctor.{u + 1, u}).map
        (BousfieldKanPointSection.sectionMap (circleCompanionBKReflectedPointMap z)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCosliceComparison
        (pointLoopDiagram (nativeCotensorInput PointedSimplicialSet.circle z).val)
        (cotensor PointedSimplicialSet.circle
          (nativeCotensorInput PointedSimplicialSet.circle z).val) =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCosliceSimplex
        (pointLoopDiagram (nativeCotensorInput PointedSimplicialSet.circle z).val)
        (cotensor PointedSimplicialSet.circle
          (nativeCotensorInput PointedSimplicialSet.circle z).val)
        ⟨σ, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.prefixOverWeight σ ≫ Functor.whiskerLeft σ
          (circleCompanionBKReflectedSection z)⟩) := by
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCosliceSimplex _ _
      ((BousfieldKanPointSection.sectionMap (circleCompanionBKReflectedPointMap z)).app
        (Opposite.op ⦋n⦌) σ) = _
    rw [BousfieldKanPointSection.sectionMap_app, circleCompanionBKReflectedPointMap_transform]
    exact (Equiv.apply_symm_apply _ _).symm
  rw [hs, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnderUncurry_yoneda]
  rfl

/-- 元の companion の coherent 錐を、元の標準 cone 単体で読む。 -/
def circleCompanionBKCoherentConeSimplex (z : Sp.{u} _⦋0⦌) {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} WalkingCospan) n) : Sp.{u} _⦋n + 1⦌ :=
  SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftPointStdSimplexIso n).inv ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u + 1})) (SSet.yonedaEquiv.symm (ULift.up σ)) ≫
      (circleCompanionBKCoherentCone z).val)

/-- この元の cone 単体は、同じ元の全切断から作った weighted cone simplex と厳密一致する。 -/
lemma circleCompanionBKCoherentConeSimplex_eq (z : Sp.{u} _⦋0⦌) {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} WalkingCospan) n) :
    circleCompanionBKCoherentConeSimplex z σ = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeSimplex
      (pointLoopDiagram (nativeCotensorInput PointedSimplicialSet.circle z).val)
      (cotensor PointedSimplicialSet.circle
        (nativeCotensorInput PointedSimplicialSet.circle z).val)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.prefixOverWeight σ ≫ Functor.whiskerLeft σ (circleCompanionBKReflectedSection z)) := by
  rw [circleCompanionBKCoherentConeSimplex, circleCompanionBKCoherentCone_simplex,
    Iso.inv_hom_id_assoc]
  exact Equiv.apply_symm_apply _ _

/-- 既存の切断点から復元した元の coherent 錐の三角形は、前工程の反転三角形そのもの。 -/
lemma circleCompanionBKCoherentConeSimplex_triangle (z : Sp.{u} _⦋0⦌) (k : WalkingPair) :
    circleCompanionBKCoherentConeSimplex z (LoopEdgewiseSection.arrow k) =
      circleCompanionReflectedTriangle z k := by
  rw [circleCompanionBKCoherentConeSimplex_eq]
  rfl

/-- 元の coherent 錐の実際の三角形の trace も、元の共通解像の三単体の左辺に一致する。 -/
lemma circleCompanionBKCoherentConeSimplex_triangle_trace (z : Sp.{u} _⦋0⦌)
    (k : WalkingPair) :
    CoherentPathCoordinates.triangleTrace
      (circleCompanionBKCoherentConeSimplex z (LoopEdgewiseSection.arrow k)) ≫
      eqToHom (congrArg (fun s : (SimplicialNerve OmegaSpectrum.{u}) _⦋2⦌ ↦
        SimplicialCategory.sHom (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩))
        (circleCompanionBKCoherentConeSimplex_triangle z k)) =
      SSet.yonedaEquiv.symm (stdSimplex.edge 3 0 1 (by decide)) ≫
        circleCompanionEdgewiseTetrahedron z k := by
  exact (CoherentPathCoordinates.triangleTrace_congr
    (circleCompanionBKCoherentConeSimplex_triangle z k)).trans
      (circleCompanionReflectedTriangle_trace z k)

end SerrePositivity.KST.Spectra.OmegaSpectrum
