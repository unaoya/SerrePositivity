module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StandardSimplexNaturality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.OneHornComparison

/-!
概要：標準一単体の全局所比較を、同じホーン側の端点へ制限する指定自然性。
方針：同じ標準点の自然性を、元のホーン表示同型で運ぶ。
規約：大域から制限された像に限定しない。
使われ方：一次元境界の二端点で指定同型を対にする。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
variable {C : Type u} [Category.{u} C] (i : Fin 2)
  (σ : (Δ[1] : SSet.{u}) ⟶ nerve C) (p q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory (nerve C))
local notation "N" => (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeCoreFunctor p.val.hom q.val.hom) ⋙
  SSet.uliftFunctor
local notation "T" => Functor.op (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.uliftOverFunctor (nerve C)) ⋙
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramOverFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram p.val.hom)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram q.val.hom)

local instance (z : (Over (nerve C))ᵒᵖ) : Quasicategory ((T).obj z) :=
  inferInstanceAs (Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map z.unop.hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram p.val.hom))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map z.unop.hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram q.val.hom))))

/-- 同じホーンの、元の標準一単体への底上の包含。 -/
def hornOneSimplexOverMap : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.horn 0 i σ ⟶ Over.mk σ :=
  Over.homMk (horn 1 i).ι rfl

/-- 標準点から元の一単体への同じ底上の写像。 -/
def hornOnePointSimplexOverMap : Over.mk (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.hornOnePointMap i σ) ⟶ Over.mk σ :=
  Over.homMk ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.hornOnePointIso i).hom ≫ (horn 1 i).ι) (Category.assoc _ _ _)

/-- 元のホーン表示同型と両包含の正方形は厳密に可換。 -/
lemma hornOnePointSimplexOverMap_comp :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.hornOnePointOverIso i σ).hom ≫ hornOneSimplexOverMap i σ =
      hornOnePointSimplexOverMap i σ := by
  apply Over.OverMorphism.ext
  rfl

/-- 全局所 Hom の同じ一単体比較は、ホーン側の端点への直接制限に自然。 -/
def cocartesianOneHornHomComparison_localNaturalityIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      ((N).map (hornOneSimplexOverMap i σ).op ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOneHornHomComparison i σ p q)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStandardSimplexHomComparison σ p q ≫
        (T).map (hornOneSimplexOverMap i σ).op) := by
  have hc : (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.hornOnePointOverIso i σ).inv ≫ hornOnePointSimplexOverMap i σ =
      hornOneSimplexOverMap i σ ≫ (Iso.refl (Over.mk σ)).hom := by
    rw [← hornOnePointSimplexOverMap_comp]
    simp only [Iso.refl_hom, Category.comp_id, Iso.inv_hom_id_assoc]
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.contravariantComparisonIso (N) (T) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.hornOnePointOverIso i σ).symm
    (Iso.refl (Over.mk σ)) (hornOneSimplexOverMap i σ) (hornOnePointSimplexOverMap i σ) hc
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStandardSimplexHomComparison (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.hornOnePointMap i σ) p q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStandardSimplexHomComparison σ p q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStandardSimplexHomComparison_overNaturalityIso
      ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.hornOnePointIso i).hom ≫ (horn 1 i).ι) σ p q (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.hornOnePointMap i σ)
      (Category.assoc _ _ _))
  apply _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq h
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOneHornHomComparison, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOneHornSourceIso_hom,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianOneHornTargetIso_hom]
    rfl
  · simp only [Iso.refl_inv, Iso.refl_hom, op_id]
    rw [(N).map_id, (T).map_id, Category.id_comp, Category.comp_id]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
