module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.FunctorSliceTerminal

/-!
概要：Fun(K, X_/z) を、Fun(K,X) の定値関手の実 slice と底の上で同値にする。
方針：関手圏内の恒等錐への全切断と、終対象を持つ right fibration の表示を使う。
規約：切断をデータとして保持する。使われ方：実評価方程式から屋根内の実比較への移送。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
variable (K : SSet.{u}) {X : SSet.{u}} (z : X _⦋0⦌)
/-- 全パラメータの恒等錐への、始域を厳密に保持する全錐切断。 -/
structure FunctorSliceRepresentation where
  coneSection : (ihom K).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm z)) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofFunctorSliceIdentity K z))
  coneSection_projection : coneSection ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection _ = 𝟙 _
/-- 全切断を使った、同じ定値終点のパラメータ関手圏の実 slice への写像。 -/
def roofFunctorSliceRepresentationMap (C : FunctorSliceRepresentation K z) :
    (ihom K).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm z)) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const (X := K) z))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.roofTerminalRepresentationMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofFunctorSliceProjection K z) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofFunctorSliceIdentity K z)
    C.coneSection ≫
      (eqToIso (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofFunctorSliceIdentity_point K z))).hom
/-- 全切断による slice 表示は、始域射影と厳密に可換する。 -/
lemma roofFunctorSliceRepresentationMap_over (C : FunctorSliceRepresentation K z) :
    roofFunctorSliceRepresentationMap K z C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection _ =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofFunctorSliceProjection K z := by
  dsimp only [roofFunctorSliceRepresentationMap]
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceOverProjection_eqTransport
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofFunctorSliceIdentity_point K z)]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.roofTerminalRepresentationMap_over _ _ _ C.coneSection_projection
/-- 全パラメータ関手圏の slice 表示は、quasicategory の同値。 -/
lemma roofFunctorSliceRepresentationMap_isQCatEquivalence [Quasicategory X]
    (C : FunctorSliceRepresentation K z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (roofFunctorSliceRepresentationMap K z C) := by
  have := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofFunctorSliceProjection_rightFibration K z
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.roofTerminalRepresentationMap_isQCatEquivalence
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofFunctorSliceProjection K z) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofFunctorSliceIdentity K z)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofFunctorSliceIdentity_isTerminal K z) C.coneSection C.coneSection_projection
  exact h.comp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso
    (eqToIso (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofFunctorSliceIdentity_point K z)))).isQCatEquivalence
/-- 任意のパラメータ集合と quasicategory 標的について、実 slice 表示が存在する。 -/
lemma functorSliceRepresentation_nonempty [Quasicategory X] :
    Nonempty (FunctorSliceRepresentation K z) := by
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection
      (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofFunctorSliceIdentity K z))) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isTerminalVertex_iff_trivialKanFibration _).mp (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofFunctorSliceIdentity_isTerminal K z)
  obtain ⟨σ, hσ⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection
    (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofFunctorSliceIdentity K z)))
  exact ⟨⟨σ, hσ⟩⟩
end SerrePositivity.InfinityCategories.Project.DerivedCategories
