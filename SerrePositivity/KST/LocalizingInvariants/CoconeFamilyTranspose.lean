module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeVertexTriangles
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.CoconeFamilyTranspose
public import SerrePositivity.KST.LocalizingInvariants.IntervalMappingFamilyTranspose
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.SimplexTerminalCoconeExtension

/-!
概要：同じ前段上の全余錐族を、パラメータ関手圏の元の全余錐へ移す。
方針：内部 Hom の厳密転置で前段と終端脚を保ち、比較同型も同じ交換で移す。
規約：終端脚は元の実辺の一次単体のまま回収する。
使われ方：回収した実分母・次辺を指定前段経路付きの全単体比較へ貼る。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

/-- 前段が同じ図式に厳密に定値な余錐族を、関手圏の元の余錐へ移す。 -/
def spanCoconeFamilyTranspose {K L X : SSet.{u}} (D : L ⟶ X)
    (F : K ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join L (Δ[0] : SSet.{u}))).obj X)
    (hF : F ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl L Δ[0])).app X = SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex D)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (D ≫ curry (snd K X)) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv K (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join L Δ[0]) X F, by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre_app, hF, spanInternalHomFlip_const]⟩

/-- 同じ終端辺の全族から、転置した元の余錐の同じ終端脚を厳密に回収する。 -/
lemma spanCoconeFamilyTranspose_last_edge {K X : SSet.{u}} {n : ℕ}
    (D : (Δ[n] : SSet.{u}) ⟶ X)
    (F : K ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[n] : SSet.{u}) Δ[0])).obj X)
    (hF : F ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) Δ[0])).app X =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex D))
    (a : K ⟶ (ihom (Δ[1] : SSet.{u})).obj X)
    (ha : F ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]))).app X =
      a ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom).app X) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeVertexLeg
      (spanCoconeFamilyTranspose D F hF) (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n))).edge =
      SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv K Δ[1] X a) := by
  have he := congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv K (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) Δ[0]) X) ha
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre_app, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre_app] at he
  change SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.yonedaEquiv.symm (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n))) (𝟙 Δ[0]) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv K (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[n] : SSet.{u}) Δ[0]) X F) = _
  rw [Equiv.symm_apply_apply, he,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- 元の固定端点 Hom の族で指定した終端脚を、同じ実関手辺として回収する。 -/
lemma spanCoconeFamilyTranspose_last_interval_edge {K X : SSet.{u}} {n : ℕ}
    (D : (Δ[n] : SSet.{u}) ⟶ X)
    (F : K ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[n] : SSet.{u}) Δ[0])).obj X)
    (hF : F ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) Δ[0])).app X =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex D)) {x y : X _⦋0⦌}
    (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y)
    (hf : F ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]))).app X =
      f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((pre (boundary 1).ι).app X)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingBoundary x y)) ≫
        (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom).app X) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeVertexLeg (spanCoconeFamilyTranspose D F hF)
      (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n))).edge = (intervalMappingFamilyEdge f).edge := by
  have he := spanCoconeFamilyTranspose_last_edge D F hF
    (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((pre (boundary 1).ι).app X)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingBoundary x y))) hf
  exact he.trans (intervalMappingFamilyEdge_edge f).symm

end SerrePositivity.KST.LocalizingInvariants
