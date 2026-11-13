module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.DGCompositionSecondUnitDiagram
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.SecondUnitSquareGeometry
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CompositionSquareEvaluation
/-!
概要：第二閉恒等入力の標準合成正方形を最大時刻による元の区間族へ同定する。
方針：全 slice 図式の表示を右 join prism で評価し、二つの切断の合成を計算する。
規約：Small 仮定なしで同じ coherent prism・全時間・元 Hom 入力を保持する。
使われ方：同じ正方形の標準三角形への制限から第二単位面の厳密退化を得る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]

lemma dgGluingDGCompositionSecondUnitSquare {K : SSet.{max u v}} {x y : E}
    (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R E x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism (Δ[1] ⊗ K) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedCompositionFamilyPrism R E f
        (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex R E (𝟙 (ForgetEnrichment.of (Complex R) y))))) =
    (α_ Δ[1] Δ[1] K).inv ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitSquareMax ▷ K) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, t, k⟩
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry _).app (Opposite.op ⦋n⦌)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism (Δ[1] ⊗ K)).app _ (s, (t, k))) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.rightMappingSpacePrism_evaluate, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.sliceOverUncurry_simplex_coordinate,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDGCompositionFamilyPrism_second_unit_diagram,
    Iso.inv_hom_id_assoc, ← SSet.yonedaEquiv_naturality,
    Equiv.apply_symm_apply]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E).map
    (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut (stdSimplex.objEquiv s).toOrderHom)).op
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E).map
      (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCompositionUnitCollapse (stdSimplex.objEquiv t).toOrderHom)).op
      (f.app _ k).val) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _)).app _
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitSquareMax.app _ (s, t)), k)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pinchedHomToIntervalMappingSpace_evaluate, ← types_comp_apply, ← Functor.map_comp]
  congr 2
  apply congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E).map
  change (SimplexCategory.mkHom ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCompositionUnitCollapse
    (stdSimplex.objEquiv t).toOrderHom).comp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut (stdSimplex.objEquiv s).toOrderHom))).op = _
  congr 1
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  exact congrArg (fun h : Fin (n + 1) →o Fin (n + 2) => h i)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSecondUnit_prism_cut (stdSimplex.objEquiv s).toOrderHom
      (stdSimplex.objEquiv t).toOrderHom)
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
