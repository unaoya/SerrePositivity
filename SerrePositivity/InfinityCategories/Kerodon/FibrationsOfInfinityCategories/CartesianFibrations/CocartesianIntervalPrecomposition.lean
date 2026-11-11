module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.EdgeCosliceFamilySquare
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IntervalCosliceSource
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.IntervalComposition
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalFunctorHom
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.SquareComposition

/-!
概要：区間を被覆する coCartesian 辺による前合成は、区間写像空間のホモトピー同値。
方針：錐の比較 span を任意の族で元の前合成と照合し、両射影の同値性を移す。
規約：通常の Hom の全単射へ弱めない。使われ方：Quillen 導来随伴の単位の各点の判定。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
noncomputable section
attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration
variable {T E : SSet.{u}} (e : (Δ[1] : SSet.{u}) ⟶ E) (y : E _⦋0⦌)

/-- 元の任意の錐の族で、始点側の写像は固定辺と終点側の写像の合成である。 -/
lemma edgeCosliceIntervalMap_composition (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection e) y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap T (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeCosliceEdge e)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (a ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeCosliceIntervalMap e y 0) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (a ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeCosliceIntervalMap e y 1) := by
  let f := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeCosliceEdge e).map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap T E))
  let c : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom T).obj E))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) ≫ e)) : T ⟶ E))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ e)) : T ⟶ E)) :=
    ⟨f.edge, f.src_eq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap_vertex T _),
      f.tgt_eq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap_vertex T _)⟩
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap T
      (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeCosliceEdge e)) =
        SSet.Truncated.HomotopyCategory.homMk c :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homMk_transport (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap_vertex T _) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap_vertex T _) f c rfl
  have hi : SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge := by
    apply SSet.stdSimplex.ext
    intro j
    fin_cases j <;> rfl
  have hq := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.homMk_comp_eq_of_square c
    (SSet.Truncated.Edge.id (X := (truncation 2).obj ((ihom T).obj E))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const y : T ⟶ E)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyEdge (a ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeCosliceIntervalMap e y 1))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyEdge (a ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeCosliceIntervalMap e y 0))
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeCosliceFamilySquare e y a) ?_ ?_ ?_ ?_
  · rw [SSet.Truncated.HomotopyCategory.homMk_id, Category.comp_id] at hq
    rw [hc]
    exact hq
  · change (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeCosliceFamilySquare e y a).app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge, _) = _
    rw [← hi]
    change SSet.yonedaEquiv (SSet.ι₀ ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeCosliceFamilySquare e y a) = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeCosliceFamilySquare_bottom, SSet.yonedaEquiv_comp]
    rfl
  · change (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeCosliceFamilySquare e y a).app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge, _) = _
    rw [← hi]
    change SSet.yonedaEquiv (SSet.ι₁ ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeCosliceFamilySquare e y a) = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeCosliceFamilySquare_top]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (X := (ihom T).obj E)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const y : T ⟶ E)) 1 = _
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one _
  · change (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeCosliceFamilySquare e y a).app (Opposite.op ⦋1⦌)
      (_, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) = _
    rw [← hi]
    change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Δ[1] ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeCosliceFamilySquare e y a) = _
    exact congrArg SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeCosliceFamilySquare_side e y a 0)
  · change (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeCosliceFamilySquare e y a).app (Opposite.op ⦋1⦌)
      (_, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) = _
    rw [← hi]
    change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[1] ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeCosliceFamilySquare e y a) = _
    exact congrArg SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeCosliceFamilySquare_side e y a 1)

/-- 二つの制限を結ぶ比較 span は、元の区間模型の前合成をホモトピーで表す。 -/
lemma edgeCosliceIntervalMap_precompose [Quasicategory E] :
    Nonempty (SSet.Homotopy
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeCosliceIntervalMap e y 0 ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPrecompose y
        (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeCosliceEdge e)))
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeCosliceIntervalMap e y 1)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom_eq_imp_homotopy
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPrecompose_family]
  simpa only [Category.id_comp] using edgeCosliceIntervalMap_composition e y
    (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection e) y))

/-- 指定端点への錐の制限が trivial Kan なら、区間模型への比較も同値である。 -/
lemma edgeCosliceIntervalMap_isQCatEquivalence [Quasicategory E] (j : Fin 2)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap e (stdSimplex.δ j) y)] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeCosliceIntervalMap e y j) := by
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap e (stdSimplex.δ j) y)).comp
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceFiberDiagramIso
      (Equiv.symm_apply_apply SSet.yonedaEquiv (stdSimplex.δ j ≫ e)).symm y)).isQCatEquivalence.comp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberToIntervalMappingSpace_isQCatEquivalence _ y))

/-- 終点側への区間写像空間比較は、任意の元の固定辺に対して同値である。 -/
lemma edgeCosliceIntervalMap_target_isQCatEquivalence [Quasicategory E] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeCosliceIntervalMap e y 0) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceTriangleTarget_trivialKanFibration e y
  exact edgeCosliceIntervalMap_isQCatEquivalence e y 0

/-- 元の固定辺が coCartesian なら、始点側への区間写像空間比較は同値である。 -/
lemma edgeCosliceIntervalMap_source_isQCatEquivalence [Quasicategory E]
    (p : E ⟶ (Δ[1] : SSet.{u})) (hp : e ≫ p = 𝟙 Δ[1])
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p (SSet.yonedaEquiv e))
    (hy : p.app (Opposite.op ⦋0⦌) y = stdSimplex.obj₀Equiv.symm (1 : Fin 2)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeCosliceIntervalMap e y 1) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceTriangleSource_trivialKanFibration p e hp he y hy
  exact edgeCosliceIntervalMap_isQCatEquivalence e y 1

/-- 元の coCartesian 辺による前合成は、上段終域への区間写像空間のホモトピー同値。 -/
lemma intervalPrecompose_isSimplicialHomotopyEquivalence_of_cocartesian
    [Quasicategory E] (p : E ⟶ (Δ[1] : SSet.{u})) (hp : e ≫ p = 𝟙 Δ[1])
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p (SSet.yonedaEquiv e))
    (hy : p.app (Opposite.op ⦋0⦌) y = stdSimplex.obj₀Equiv.symm (1 : Fin 2)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPrecompose y
      (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeCosliceEdge e))) := by
  obtain ⟨H⟩ := edgeCosliceIntervalMap_precompose e y
  have ht := edgeCosliceIntervalMap_target_isQCatEquivalence e y
  have hs := edgeCosliceIntervalMap_source_isQCatEquivalence e y p hp he hy
  have hcomp := hs.ofFunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy H).symm
  exact (ht.cancel_left hcomp).isSimplicialHomotopyEquivalence

end
end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
