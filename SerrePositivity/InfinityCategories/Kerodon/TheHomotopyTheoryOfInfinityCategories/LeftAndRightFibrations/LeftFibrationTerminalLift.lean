module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CocartesianTerminalBoundary
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.ContractibleKan

/-!
概要：終対象上の可縮 fiber の指定点を、left fibration の全空間の終対象へ移す。
方針：元の left horn の充填から cocartesian 輸送を取り、相対終点境界充填を合成する。
規約：元の fiber の指定点を保持し、全空間の弱可縮性だけで代用しない。
使われ方：元の図式を固定した錐族の、同じ持ち上げ錐の極限性。

対応節は Kerodon 4.2（Tag 014H）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations

/-- left fibration の元の持ち上げは、同じ全空間で cocartesian 輸送を与える。 -/
lemma leftFibration_cocartesianHornStructure {E B : SSet.{u}} (p : E ⟶ B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianHornFibration p := by
  refine { mem := InnerFibration.mem, exists_lift := ?_ }
  intro x b a
  obtain ⟨F, hF₀, hFp⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.leftFibration_liftEdge_source p x a
  let e : SSet.Truncated.Edge (X := (truncation 2).obj E) x
      (E.δ 0 (SSet.yonedaEquiv F)) :=
    { edge := SSet.yonedaEquiv F
      src_eq := by
        change E.δ 1 (SSet.yonedaEquiv F) = x
        rw [← stdSimplex.yonedaEquiv_δ_comp, hF₀]
        exact SSet.yonedaEquiv.apply_symm_apply x
      tgt_eq := rfl }
  refine ⟨_, e, ?_, ?_⟩
  · change p.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv F) = a.edge
    rw [← SSet.yonedaEquiv_comp, hFp]
    exact SSet.yonedaEquiv.apply_symm_apply a.edge
  · intro n σ β _ hw
    have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := p) _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftHornInclusions.intro (0 : Fin (n + 3)) (by change (0 : ℕ) < n + 2; omega))
    let sq : CommSq σ (horn (n + 2) 0).ι p β := ⟨hw⟩
    exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

/-- 相対終点境界充填と同じ像の終対象性から、元の指定点自身の終対象性を得る。 -/
lemma isTerminalVertex_of_terminalBoundary_image {E B : SSet.{u}} (p : E ⟶ B)
    {x : E _⦋0⦌} (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting p x)
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (p.app (Opposite.op ⦋0⦌) x)) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex x := by
  intro n a ha
  have hend : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ (a ≫ p) =
      SSet.yonedaEquiv.symm (p.app (Opposite.op ⦋0⦌) x) := by
    rw [← Category.assoc, ha, SSet.yonedaEquiv_symm_comp]
  obtain ⟨β, hβ⟩ := hp n (a ≫ p) hend
  obtain ⟨F, hF, _⟩ := hx n a β ha ⟨hβ.symm⟩
  exact ⟨F, hF⟩

/-- 終対象上の可縮 fiber の元の指定点は、全空間内でも終対象。 -/
lemma leftFibration_isTerminalVertex_of_contractibleFiber
    {E B : SSet.{u}} [Quasicategory E] [Quasicategory B]
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (b : B _⦋0⦌) (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex b)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b)) (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex x.val := by
  have := leftFibration_cocartesianHornStructure p
  have hx := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.terminalBoundaryLifting_of_isTerminalVertex_fiber p b x (h.isTerminalVertex x)
  apply isTerminalVertex_of_terminalBoundary_image p hx
  have hp : p.app (Opposite.op ⦋0⦌) x.val = b := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero] using x.property
  rwa [hp]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "5.5.6.6" (partial := special) "仮定：coCartesian p:E→B とファイバー・基底で k 切断な点（Lean が強い：k=−2、p は left fibration、指定ファイバーは可縮 Kan）。結論：同じファイバーの指定点は元の全空間 E の終対象、従って −2 切断（この場合に一致）。元の点を保持し、全空間の弱可縮性だけで代用しない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibration_isTerminalVertex_of_contractibleFiber
