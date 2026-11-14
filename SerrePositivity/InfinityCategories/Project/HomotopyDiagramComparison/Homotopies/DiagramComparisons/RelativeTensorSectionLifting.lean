module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.TensorFamilyCurrying
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibrationLocalFamily
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.UniversalScaffoldEvaluation

/-!
概要：相対 Hom の頂点 fiber の可縮性から、元の積図式の切断制限の全境界充填を得る。
方針：全パラメータの指数則と相対持ち上げを、元の図式の全境界へ移す。
規約：底 K は任意の単体集合。使われ方：HTT 5.5.4.5(2) の余極限比較辺の局所性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 各頂点の相対 Hom fiber が可縮なら、積図式の切断の元の制限は全境界を持ち上げる。 -/
lemma relativeFunctorPre_tensor_trivial_of_vertexFibers {A D K E B : SSet.{u}}
    (i : D ⟶ A) [Mono i] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration p]
    (sq : internalHom.PullbackObjObj i p) (g : A ⊗ K ⟶ B)
    (h : ∀ (k : K _⦋0⦌) (b : sq.pt _⦋0⦌),
      sq.snd.app (Opposite.op ⦋0⦌) b = (curry g).app (Opposite.op ⦋0⦌) k →
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber sq.π b)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p g (i ▷ K)) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).2
  intro n
  constructor
  intro u v s
  let j := K ◁ (boundary n).ι
  have : Mono j := (tensorLeft K).map_mono (boundary n).ι
  let d := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.tensorFamilyCurry (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry v)
  let l := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.tensorFamilyCurry (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry u)
  have hd : d ≫ (ihom D).map p = (fst K Δ[n] ≫ curry g) ≫ (pre i).app B := by
    rw [← _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.tensorFamilyCurry_post, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_projection,
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.tensorFamilyCurry_constant, ← curry_pre_app, Category.assoc]
  have hl : l ≫ (pre i).app E = j ≫ d := by
    have he := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry s.w
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorUncurry_pre,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorUncurry_parameter] at he
    change _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.tensorFamilyCurry (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry u) ≫ (pre i).app E = _
    rw [← _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.tensorFamilyCurry_source, he, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.tensorFamilyCurry_parameter]
  have hb : l ≫ (ihom A).map p = j ≫ fst K Δ[n] ≫ curry g := by
    change _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.tensorFamilyCurry (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry u) ≫ (ihom A).map p = _
    rw [← _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.tensorFamilyCurry_post, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_projection, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.tensorFamilyCurry_constant]
    rfl
  obtain ⟨L, hLj, hLd, hLb⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.relativeHomFamily_exists_extension_over_base
    i p sq (curry g) h j d (fst K Δ[n]) hd l hl hb
  have hLp : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.tensorFamilyUncurry L ≫ p = fst (A ⊗ K) Δ[n] ≫ g := by
    apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.tensorFamilyCurry_injective
    rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.tensorFamilyCurry_post, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.tensorFamilyCurry_uncurry, hLb, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.tensorFamilyCurry_constant]
  let W := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorCurry (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.tensorFamilyUncurry L) hLp
  refine CommSq.HasLift.mk' { l := W, fac_left := ?_, fac_right := ?_ }
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_injective p g
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorUncurry_parameter,
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_curry]
    apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.tensorFamilyCurry_injective
    rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.tensorFamilyCurry_parameter, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.tensorFamilyCurry_uncurry, hLj]
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_injective p ((i ▷ K) ≫ g)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorUncurry_pre,
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_curry]
    apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.tensorFamilyCurry_injective
    rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.tensorFamilyCurry_source, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.tensorFamilyCurry_uncurry, hLd]

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
