module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.OneBoundaryOriginalTarget
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.PairedKanFunctorIso

/-!
概要：実際の一次元境界全体の比較を、元の大域の全 Hom 作用へ指定同型で戻す。
方針：両端の既存の指定同型を対にし、同じ target 積分解の逆で境界へ戻す。
規約：同じ比較写像と元の分類主写像を保持する。
使われ方：高次境界の比較と共有境界での整合性の初期値。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.OneBoundaryOriginal
variable {C : Type u} [Category.{u} C] (i : Fin 2) (σ : (Δ[1] : SSet.{u}) ⟶ nerve C)
  (p q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory (nerve C))
local notation "P" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram p.val.hom
local notation "Q" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram q.val.hom

local instance (z : Over ((SSet.uliftFunctor.{u + 1, u}).obj (nerve C))) :
    KanComplex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramOverFunctor P Q).obj (Opposite.op z)) :=
  inferInstanceAs (KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (z.hom ≫ P)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (z.hom ≫ Q))))

/-- 同じ一次元境界比較は、元の全 Hom 作用の境界制限と指定関手同型で可換。 -/
def cocartesianOneBoundaryHomComparison_originalIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeLiftRestriction p.val.hom q.val.hom
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.apex 0 σ) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOneBoundaryHomComparison i σ p q)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStraighteningHomInterval p q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramRestriction
        ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.apex 0 σ).hom) P Q) := by
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeLiftRestriction p.val.hom q.val.hom
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.apex 0 σ) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOneBoundaryHomComparison i σ p q) ≫
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOneBoundaryIntervalProductIso i σ P Q).hom)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStraighteningHomInterval p q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramRestriction
        ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.apex 0 σ).hom) P Q) ≫
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOneBoundaryIntervalProductIso i σ P Q).hom) := by
    apply _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.pairedKanFunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStandardSimplexHomComparison_originalIso (stdSimplex.δ i ≫ σ) p q)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOneHornHomComparison_originalIso i σ p q))
    · simpa only [Over.mk_hom, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.face, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramOverFunctor] using
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOneBoundaryHomComparison_originalSourceProduct i σ p q).symm
    · simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOneBoundaryOriginalFaceAction,
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOneBoundaryOriginalHornAction, Over.mk_hom, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.face,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramOverFunctor] using
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOneBoundaryHomComparison_originalTargetProduct i σ p q).symm
  apply _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq
    (h.postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOneBoundaryIntervalProductIso i σ P Q).inv)
  · rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.OneBoundaryOriginal
