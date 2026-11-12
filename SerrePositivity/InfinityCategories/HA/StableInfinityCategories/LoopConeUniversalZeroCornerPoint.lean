module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopConeUniversalSourceInitial
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopConeZeroCornerDiagram

/-!
概要：元の普遍 loop 錐の指定点の始対象性と、同じ零隅四角形への移送。
方針：固定 cospan の終対象の自己比較と、実 classifier・選択忘却を接続する。
規約：最後の全四角形図式を厳密に保つ。使われ方：同じ loop 四角形の押し出し性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 元の普遍 loop 錐の同じ指定点と四角形を保つ比較。 -/
lemma loopConeUniversalZeroCornerPoint_isInitial {X : SSet.{u}} [Quasicategory X]
    [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex X] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X] (s : X ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X)
    (hs : s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0))
    {y : X _⦋0⦌} (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopSquare y) :
    let x := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneFamilyApex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan t.square)).app
      (Opposite.op ⦋0⦌) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.sliceConeFamilyMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan t.square)).app
        (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone t.square))
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeZeroCornerSourceFiberMap X x).app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeFixedApexSourceLift t x).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeUniversalFixedApexPoint t))) := by
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan t.square
  let c := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.sliceConeFamilyMap p).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone t.square)
  let x := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneFamilyApex p).app (Opposite.op ⦋0⦌) c
  let e := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeZeroCornerSourceFiberMap_isQCatEquivalence X x).choose
  exact e.map_isInitialVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeUniversalSourcePoint_isInitial s hs hΩ t)


/-- 元の普遍 loop 錐の同じ指定点と四角形を保つ比較。 -/
lemma loopConeUniversalZeroCornerPoint_square {X : SSet.{u}} [Quasicategory X]
    {y : X _⦋0⦌} (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopSquare y) :
    let x := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneFamilyApex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan t.square)).app
      (Opposite.op ⦋0⦌) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.sliceConeFamilyMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan t.square)).app
        (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone t.square))
    ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeZeroCornerSourceFiberMap X x).app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeFixedApexSourceLift t x).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeUniversalFixedApexPoint t))).val.val = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex t.square := by
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan t.square
  let c := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.sliceConeFamilyMap p).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone t.square)
  let x := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneFamilyApex p).app (Opposite.op ⦋0⦌) c
  let v := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeUniversalFixedApexPoint t
  let Z := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X)
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroCornerSquareVertex).ι
  have hh : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeFixedApexSourceLift t x ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeZeroCornerSourceFiberMap X x) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquareSource X) x ≫ Z =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedApexConeFamilyEvaluation p x ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareConeFunctorIso X).inv := by
    dsimp only [Z]
    simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeZeroCornerSourceFiberMap,
      reassoc_of% _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι, reassoc_of% _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeFixedApexSourceLift_ι,
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeZeroCornerForget_diagram, reassoc_of% _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeFixedApexLift_diagram]
    rfl
  have hv : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedApexConeFamilyEvaluation p x).app (Opposite.op ⦋0⦌) v =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone t.square).val := by
    change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.sliceConeFamilyMap p).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone t.square)).val = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.sliceConeFamilyMap_app_zero]
    rfl
  have he := ConcreteCategory.congr_hom (NatTrans.congr_app hh (Opposite.op ⦋0⦌)) v
  change ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeZeroCornerSourceFiberMap X x).app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeFixedApexSourceLift t x).app (Opposite.op ⦋0⦌) v)).val.val =
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareConeFunctorIso X).inv.app (Opposite.op ⦋0⦌)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedApexConeFamilyEvaluation p x).app (Opposite.op ⦋0⦌) v) at he
  rw [hv] at he
  refine he.trans ?_
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.hom ≫ t.square) = _
  rw [Iso.inv_hom_id_assoc]
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
