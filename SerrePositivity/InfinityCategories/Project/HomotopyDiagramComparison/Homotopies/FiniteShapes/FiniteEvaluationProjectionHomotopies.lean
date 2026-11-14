module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.FiniteShapes.FiniteEvaluationOuterProjections
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.CoherentDiagrams.CoherentTrianglePointEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

/-!
概要：元の反復射影の全評価 Kan 脚を、元の反復 Kan 積の全射影とホモトピーで比較する。
方針：後続脚の元の選択三角形を評価し、snd と帰納仮定を同じ向きで続ける。
規約：元の頂点・脚の辺・選択済み合成三角形を保持する。
使われ方：元の評価錐の点ごとの極限性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 元の後続評価脚は、元の snd と元の tail 評価脚の合成へ同じ三角形で比較される。 -/
def finiteFunctorEvaluationKanLeg_succ_homotopy (n : ℕ) {B : SSet.{u}}
    (F : Fin (n + 1 + 1) → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}))
    (b : ((SSet.uliftFunctor.{u + 1, u}).obj B) _⦋0⦌) (j : Fin (n + 1)) :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFunctorEvaluationKanLeg (n + 1) F b (Discrete.mk (ULift.up j.succ)))
      (snd (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFunctorKanValues (n + 1) F b 0).obj
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteKanProductObject n (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFunctorKanValues n (fun i ↦ F i.succ) b)).obj ≫
          _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFunctorEvaluationKanLeg n (fun i ↦ F i.succ) b (Discrete.mk (ULift.up j))) := by
  let G := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProduct n (fun i ↦ F i.succ)
  let x := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProductSndVertex (F 0) G
  let y := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentProjectionVertex n (fun i ↦ F i.succ) j
  let T := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationVertexTriangle (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProduct (n + 1) F)
    G (F j.succ) x y
  refine _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransformationTriangleAtHomotopy _ G (F j.succ) x y T b
    (show _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteKanProductObject (n + 1) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFunctorKanValues (n + 1) F b) ⟶
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteKanProductObject n (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFunctorKanValues n (fun i ↦ F i.succ) b) from
        snd (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFunctorKanValues (n + 1) F b 0).obj
          (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteKanProductObject n (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFunctorKanValues n (fun i ↦ F i.succ) b)).obj)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFunctorEvaluationKanLeg n (fun i ↦ F i.succ) b (Discrete.mk (ULift.up j)))
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFunctorEvaluationKanLeg (n + 1) F b (Discrete.mk (ULift.up j.succ))) ?_ ?_ ?_
  · exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFunctorTailSnd_edge n F b
  · exact (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFunctorEvaluationKanLeg_edge n (fun i ↦ F i.succ) b
      (Discrete.mk (ULift.up j))).symm
  · exact (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFunctorEvaluationKanLeg_edge (n + 1) F b
      (Discrete.mk (ULift.up j.succ))).symm

/-- 元の全評価 Kan 脚は、元の反復 Kan 積の各射影にホモトピック。 -/
lemma finiteFunctorEvaluationKanLeg_projection_homotopy (n : ℕ) {B : SSet.{u}}
    (F : Fin (n + 1) → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}))
    (b : ((SSet.uliftFunctor.{u + 1, u}).obj B) _⦋0⦌)
    (i : Discrete (ULift.{u} (Fin (n + 1)))) :
    Nonempty (SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFunctorEvaluationKanLeg n F b i)
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProjection n (fun j ↦ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFunctorKanValues n F b j).obj)
        i.as.down)) := by
  rcases i with ⟨⟨i⟩⟩
  induction n with
  | zero =>
    have hi : i = 0 := Fin.eq_zero i
    subst i
    rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFunctorEvaluationKanLeg_zero]
    exact ⟨_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl _⟩
  | succ n ih =>
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFunctorEvaluationKanLeg_first]
      exact ⟨_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl _⟩
    · let a := snd (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFunctorKanValues (n + 1) F b 0).obj
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteKanProductObject n (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFunctorKanValues n (fun k ↦ F k.succ) b)).obj
      let H := finiteFunctorEvaluationKanLeg_succ_homotopy n F b j
      let L := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (Classical.choice (ih (fun k ↦ F k.succ) j)) a
      have e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
          (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFunctorEvaluationKanLeg (n + 1) F b (Discrete.mk (ULift.up j.succ)))
          (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProjection (n + 1)
            (fun k ↦ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFunctorKanValues (n + 1) F b k).obj) j.succ) :=
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy H) ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy L
      exact ⟨e.simplicialHomotopy⟩

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
