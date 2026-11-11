module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FiniteSliceDiagramApproximation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FiniteNullSpanWeakContractibility

/-! # 終対象付き右ファイブレーションへの引き戻しの弱可縮性

概要：有限対充填を持つ射の引き戻しは、右側に終対象があれば弱可縮である。
方針：有限図式を写像錐の始点へ比較し、錐の収縮と合わせて零ホモトピーの span を作る。
規約：引き戻し自体の Kan 性を要求しない。使われ方：Quillen A の slice 条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits SSet
open scoped _root_.Simplicial

/-- 終対象付き右ファイブレーションへの引き戻しは、有限対充填条件の下で弱可縮。 -/
lemma HasFiniteHomotopyRelativeFillers.weaklyContractiblePullback
    {E Y Q : SSet.{u}} {F : E ⟶ Q} (hF : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.HasFiniteHomotopyRelativeFillers F)
    (p : Y ⟶ Q) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration p] {x : Y _⦋0⦌} (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (pullback F p) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.isWeaklyContractible_of_finiteNullSpans
  intro K _ d
  obtain ⟨w, ⟨B⟩⟩ := hF.finitePullbackConeApproximation p hx d
  let u := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.finiteMappingCylinderSource (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.finiteConeMap K) ≫ w
  let z := (pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.finiteConeMap K)) ≫ w
  let q := z.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0)
  have he : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.finiteConeMap K ≫ pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.finiteConeMap K)) ≫ w =
      SSet.const q := by
    rw [Category.assoc]
    change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.finiteConeMap K) ≫ z = _
    dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.finiteConeMap]
    rw [SSet.const_comp]
  exact ⟨u, q, ⟨B⟩, ⟨_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.finiteMappingCylinderHomotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.finiteConeMap K)) w) rfl he⟩⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
