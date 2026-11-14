module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGQuotientThickKernelCriterion
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGFullKernelStability
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.ResolvedDGQuotientFlatKernel
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExactFunctorKernelEdges
/-!
概要：同じ実平坦商の核を、tria の retract 閉包から新しい小 dg 核として構成する。
方針：既存の平坦分解と商を保持し、実零頂点の反映を新核の本質像へ接続する。
規約：旧安定閉包・指定零化集合・Verdier 辺は変更せず、新名だけを追加する。
使われ方：D-16 の Sp 向け kernel 欄と商の反転飽和の同定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded DGQuotient SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]

abbrev resolvedDGQuotientThickFlatKernel (P : Set D) :=
  _root_.SerrePositivity.DifferentialGraded.DGFullSubcategory (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R D)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgThickClosureProperty R (DGCategoryCellResolution.Source R D)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R D P))

lemma resolvedDGQuotientThickFlatKernel_small (P : Set D) :
    Small.{u} (resolvedDGQuotientThickFlatKernel R D P) := inferInstance

def resolvedDGQuotientThickFlatKernelInclusion (P : Set D) :
    _root_.SerrePositivity.DifferentialGraded.DGFunctor R (resolvedDGQuotientThickFlatKernel R D P)
      (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R D) :=
  _root_.SerrePositivity.DifferentialGraded.dgFullSubcategoryInclusion R _ _

def resolvedDGQuotientThickKernelInclusion (P : Set D) :
    _root_.SerrePositivity.DifferentialGraded.DGFunctor R (resolvedDGQuotientThickFlatKernel R D P) D :=
  (resolvedDGQuotientThickFlatKernelInclusion R D P).comp
    (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R D)

lemma resolvedDGQuotientProjection_vertex_isZero_iff_thick (P : Set D)
    (x : _root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R D) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientProjection R D P).app
      (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)) ↔
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgThickClosureProperty R (DGCategoryCellResolution.Source R D)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R D P) x := by
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (inclusion R (DGCategoryCellResolution.Source R D)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R D P))).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)) ↔ _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotient_vertex_isZero_iff_thick R _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotient_localKFlat R D P) x

lemma resolvedDGQuotientProjection_zero_iff_thickEssentialImage (P : Set D)
    (b : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGCategoryCellResolution.Source R D)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientProjection R D P).app (Opposite.op ⦋0⦌) b) ↔
      ∃ a : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (resolvedDGQuotientThickFlatKernel R D P)) _⦋0⦌,
        Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (resolvedDGQuotientThickFlatKernelInclusion R D P)).app
            (Opposite.op ⦋0⦌) a) b) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullKernel_zero_iff_essentialImage R _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientProjection R D P)
    (fun x => (resolvedDGQuotientProjection_vertex_isZero_iff_thick R D P x).symm) b

lemma resolvedDGQuotientProjection_ulift_zero_iff_thickEssentialImage (P : Set D)
    (b : ((SSet.uliftFunctor.{w}).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGCategoryCellResolution.Source R D))) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (((SSet.uliftFunctor.{w}).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientProjection R D P)).app
      (Opposite.op ⦋0⦌) b) ↔
      ∃ a : ((SSet.uliftFunctor.{w}).obj
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (resolvedDGQuotientThickFlatKernel R D P))) _⦋0⦌,
        Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
          (((SSet.uliftFunctor.{w}).map
            (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (resolvedDGQuotientThickFlatKernelInclusion R D P))).app
              (Opposite.op ⦋0⦌) a) b) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullKernel_ulift_zero_iff_essentialImage R _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientProjection R D P)
    (fun x => (resolvedDGQuotientProjection_vertex_isZero_iff_thick R D P x).symm) b

lemma resolvedDGQuotientThickFlatKernel_isStable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D] (P : Set D) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (resolvedDGQuotientThickFlatKernel R D P)) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolutionSource_isDGPretriangulated R D
  let := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Pretriangulated.dgNerve_isStable_of_pretriangulated R (DGCategoryCellResolution.Source R D)
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientNerve_isStable R D P
  let hq : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientProjection R D P) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection_isExactFunctor R _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotient_localKFlat R D P)
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullKernelNerve_isStable R _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientProjection R D P)
    (fun x => (resolvedDGQuotientProjection_vertex_isZero_iff_thick R D P x).symm)

lemma resolvedDGQuotientThickFlatKernelInclusion_isExactFunctor
    [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D] (P : Set D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (resolvedDGQuotientThickFlatKernelInclusion R D P)) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolutionSource_isDGPretriangulated R D
  let := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Pretriangulated.dgNerve_isStable_of_pretriangulated R (DGCategoryCellResolution.Source R D)
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientNerve_isStable R D P
  let hq : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientProjection R D P) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection_isExactFunctor R _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotient_localKFlat R D P)
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullKernelInclusion_isExactFunctor R _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientProjection R D P)
    (fun x => (resolvedDGQuotientProjection_vertex_isZero_iff_thick R D P x).symm)

lemma resolvedDGQuotientThickFlatKernelInclusion_isFullyFaithful (P : Set D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (resolvedDGQuotientThickFlatKernelInclusion R D P)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSubcategoryInclusionNerve_isFullyFaithful R _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories
