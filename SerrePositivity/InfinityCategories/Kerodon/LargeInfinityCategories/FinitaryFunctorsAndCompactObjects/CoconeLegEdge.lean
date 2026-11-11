module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeUnitCylinder
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinComparisonNaturality
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FunctorPrismFiber
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreCoconeLeg

/-!
概要：元の余錐変換を各頂点で評価した辺は、元の指定余錐の同じ脚。
方針：元の全円柱の一点での値を、点の join 円柱の自然性で計算する。
規約：辺の類だけでなく元の全一単体の厳密な一致を保つ。
使われ方：元の fiber 写像の制限を、元の余錐脚による実輸送へ同定する。

対応節は Kerodon 9.2（Tag 0639）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects
variable {B X : SSet.{u}} {F : B ⟶ X}

/-- 元の余錐変換の同じ全辺を、元の底の指定頂点で評価する。 -/
def coconeTransportLeg (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F) (b : B _⦋0⦌) :
    X.Edge (F.app (Opposite.op ⦋0⦌) b) c.vertex :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorEdgeAt (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeTransformationVertex c)) b).ofEq rfl
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero c.vertex)

/-- 元の円柱を指定点で評価した辺は、元の指定余錐脚の全一単体そのもの。 -/
lemma coconeHomotopyLeg_edge (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F) (b : B _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeTransformationHomotopy c) b).edge =
      (c.leg (SSet.yonedaEquiv.symm b)).edge := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeTransformationHomotopy c).h.app (Opposite.op ⦋1⦌)
    ((SSet.Truncated.Edge.id (X := (truncation 2).obj B) b).edge,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) = _
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeTransformationHomotopy_h]
  apply congrArg (c.val.app (Opposite.op ⦋1⦌))
  let z := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))) 1
  have h := congrArg (fun q :
      ((Δ[0] : SSet.{u}) ⊗ Δ[1]) ⊗ Δ[0] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join B Δ[0] =>
        q.app (Opposite.op ⦋1⦌) ((z, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge), z))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap_naturality (SSet.yonedaEquiv.symm b) (𝟙 (Δ[0] : SSet.{u})))
  have sub (r : ℕ) : Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj (Δ[0] : SSet.{u}) r) := by
    cases r with
    | zero => exact inferInstanceAs (Subsingleton PUnit)
    | succ r =>
      constructor
      intro a b
      apply ULift.ext
      exact @Subsingleton.elim (⦋r⦌ ⟶ ⦋0⦌) inferInstance a.down b.down
  have hz : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap (Δ[0] : SSet.{u}) Δ[0]).app (Opposite.op ⦋1⦌)
      ((z, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge), z) =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv.app (Opposite.op ⦋1⦌)
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap_app]
    refine _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.ext _ _ ?_ ?_ ?_
    · rfl
    · exact (sub _).elim _ _
    · exact (sub _).elim _ _
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap B Δ[0]).app (Opposite.op ⦋1⦌)
      (((SSet.yonedaEquiv.symm b).app (Opposite.op ⦋1⦌) z,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge), z) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.yonedaEquiv.symm b) (𝟙 Δ[0])).app (Opposite.op ⦋1⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap (Δ[0] : SSet.{u}) Δ[0]).app (Opposite.op ⦋1⦌)
        ((z, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge), z)) at h
  rw [hz] at h
  have hb : (SSet.yonedaEquiv.symm b).app (Opposite.op ⦋1⦌) z =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant b 1 := by
    rw [SSet.yonedaEquiv_symm_app]
    exact congrArg (fun α : ⦋1⦌ ⟶ ⦋0⦌ => B.map α.op b) (Subsingleton.elim _ _)
  rw [hb] at h
  have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge = SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) := by
    apply ULift.ext
    apply SimplexCategory.Hom.ext
    ext i
    fin_cases i <;> rfl
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap B Δ[0]).app (Opposite.op ⦋1⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant b 1, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge), _) = _
  rw [ht] at h ⊢
  convert h using 1
  · apply congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap B Δ[0]).app (Opposite.op ⦋1⦌))
    refine Prod.ext ?_ ?_
    · rfl
    · exact (sub 2).elim _ _
  · apply congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.yonedaEquiv.symm b) (𝟙 (Δ[0] : SSet.{u}))).app
      (Opposite.op ⦋1⦌))
    apply congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv.app (Opposite.op ⦋1⦌))
    apply ULift.ext
    apply SimplexCategory.Hom.ext
    rfl

/-- 同じ変換の全評価辺も、元の余錐脚の全一単体を厳密に回収する。 -/
lemma coconeTransportLeg_edge (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F) (b : B _⦋0⦌) :
    (coconeTransportLeg c b).edge = (c.leg (SSet.yonedaEquiv.symm b)).edge := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt b).app (Opposite.op ⦋1⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeTransformationVertex c)).edge = _
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_edge
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeTransformationVertex c)).toTruncated b).symm.trans
      (coconeHomotopyLeg_edge c b)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects
