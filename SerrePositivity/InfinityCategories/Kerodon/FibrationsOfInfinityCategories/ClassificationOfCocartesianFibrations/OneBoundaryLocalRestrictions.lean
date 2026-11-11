module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.OneBoundaryLocalNaturality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CellAttachmentFibrations

/-!
概要：任意の一単体上の全局所 Hom の、元の境界への両側の制限と Kan 性。
方針：単射な標準境界包含に元の制限の充填性を適用する。
規約：底への一単体写像の単射性を要求しない。
使われ方：任意の一単体の両端固定 Hom 比較。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
variable {C : Type u} [Category.{u} C]
  (σ : (Δ[1] : SSet.{u}) ⟶ nerve C) (p q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory (nerve C))

/-- 分類先の同じ宇宙持ち上げ済み反変図式の全ての値は Kan。 -/
instance cocartesianIntervalLiftOverFunctor_obj_kan (z : Over (nerve C)) : KanComplex
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.uliftOverFunctor (nerve C)).op ⋙
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramOverFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram p.val.hom)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram q.val.hom)).obj (Opposite.op z)) :=
  inferInstanceAs (KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map z.hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram p.val.hom))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map z.hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram q.val.hom))))

/-- 元の一単体上の全 native Hom の同じ境界への制限。 -/
def cocartesianOneBoundaryLocalSourceRestriction :=
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeCoreFunctor p.val.hom q.val.hom) ⋙
    SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.boundarySimplexOverMap 0 σ).op

/-- 元の一単体上の分類先 Hom の同じ境界への制限。 -/
def cocartesianOneBoundaryLocalTargetRestriction :=
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.uliftOverFunctor (nerve C)).op ⋙
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramOverFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram p.val.hom)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram q.val.hom)).map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.boundarySimplexOverMap 0 σ).op

/-- 元の native Hom の同じ境界制限は Kan fibration。 -/
instance cocartesianOneBoundaryLocalSourceRestriction_fibration :
    Fibration (cocartesianOneBoundaryLocalSourceRestriction σ p q) := by
  have : Mono (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.boundarySimplexOverMap 0 σ).left := inferInstanceAs (Mono (boundary 1).ι)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeLiftPre_fibration p.val.hom q.val.hom (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.boundarySimplexOverMap 0 σ)

/-- 元の分類先 Hom の同じ境界制限も Kan fibration。 -/
instance cocartesianOneBoundaryLocalTargetRestriction_fibration :
    Fibration (cocartesianOneBoundaryLocalTargetRestriction σ p q) := by
  have : Mono (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.boundarySimplexOverMap 0 σ).left := inferInstanceAs (Mono (boundary 1).ι)
  have : Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.uliftOverMorphism.{u, u + 1} (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.boundarySimplexOverMap 0 σ)).left :=
    SimplicialModel.UniverseLift.mono_map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.boundarySimplexOverMap 0 σ).left
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramOverPre_fibration _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.uliftOverMorphism (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.boundarySimplexOverMap 0 σ))

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
