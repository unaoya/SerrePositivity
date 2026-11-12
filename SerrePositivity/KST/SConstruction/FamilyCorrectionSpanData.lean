module
public import SerrePositivity.KST.SConstruction.FamilyChainCompositeData
public import SerrePositivity.KST.SConstruction.FamilyChainTraceFaithfulness
public import SerrePositivity.KST.SConstruction.FamilyCompStructRealization

/-! # 同じ元の始点からの二補正列を結ぶ実比較円柱
概要：二つの全補正列の保存済み合成円柱を二面に持つ実比較三角形を構成する。
方針：Kan 内部 Hom で元の span を実合成し、空の二列には定数円柱を選ぶ。
規約：元の二円柱全体を保持し、零段に非定数な null loop を追加しない。
使われ方：直接厳密化と BF 合成の各段を比較する元の全パラメータの円柱。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 元の二円柱と、その両終点間の実比較円柱・実三角形。 -/
structure FamilyCorrectionSpanData {U E : SSet.{u}} {s a b : U ⟶ E}
    (H : SSet.Homotopy s a) (K : SSet.Homotopy s b) where
  /-- 元の二終点の間の実比較円柱。 -/
  homotopy : SSet.Homotopy a b
  /-- 二つの元の円柱を全体として二面に保つ実三角形。 -/
  triangle : SSet.Edge.CompStruct
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H))
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy homotopy))
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy K))

/-- 元の全 span 三角形を同じパラメータ付き実二単体へ戻す。 -/
def FamilyCorrectionSpanData.realization {U E : SSet.{u}} {s a b : U ⟶ E}
    {H : SSet.Homotopy s a} {K : SSet.Homotopy s b} (D : FamilyCorrectionSpanData H K) :=
  familyCompStructRealization D.triangle

/-- 同じデータの第一面は元の第一円柱全体。 -/
lemma FamilyCorrectionSpanData.realization_first {U E : SSet.{u}} {s a b : U ⟶ E}
    {H : SSet.Homotopy s a} {K : SSet.Homotopy s b} (D : FamilyCorrectionSpanData H K) :
    (U ◁ stdSimplex.δ 2) ≫ D.realization = H.h :=
  familyCompStructRealization_first D.triangle

/-- 同じデータの第二面は実比較円柱全体。 -/
lemma FamilyCorrectionSpanData.realization_comparison {U E : SSet.{u}} {s a b : U ⟶ E}
    {H : SSet.Homotopy s a} {K : SSet.Homotopy s b} (D : FamilyCorrectionSpanData H K) :
    (U ◁ stdSimplex.δ 0) ≫ D.realization = D.homotopy.h :=
  familyCompStructRealization_second D.triangle

/-- 同じデータの合成面は元の第二円柱全体。 -/
lemma FamilyCorrectionSpanData.realization_composite {U E : SSet.{u}} {s a b : U ⟶ E}
    {H : SSet.Homotopy s a} {K : SSet.Homotopy s b} (D : FamilyCorrectionSpanData H K) :
    (U ◁ stdSimplex.δ 1) ≫ D.realization = K.h :=
  familyCompStructRealization_direct D.triangle

/-- 元の二円柱から、指定した全二辺を保つ実比較円柱と三角形を構成する。 -/
def familySpanComparisonData {U E : SSet.{u}} [KanComplex E] {s a b : U ⟶ E}
    (H : SSet.Homotopy s a) (K : SSet.Homotopy s b) : FamilyCorrectionSpanData H K := by
  let d := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.kanMappingSpanComposition
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H))
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy K))
  let V := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge d.edge.toTruncated
  have hV : SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy V) =
      SSet.HomotopyCategory.homMk d.edge := by
    congr 1
    apply SSet.Truncated.Edge.ext
    change SSet.yonedaEquiv (curry (uncurry (SSet.yonedaEquiv.symm d.edge.edge))) = _
    rw [curry_uncurry, Equiv.apply_symm_apply]
    rfl
  refine ⟨V, SSet.Edge.CompStruct.ofTruncated
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.compStruct_nonempty_of_homMk_fac ?_).some⟩
  change SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H) ≫
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy V) =
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy K)
  rw [hV]
  have hinv : SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H) ≫ SSet.HomotopyCategory.homMk d.inverse = 𝟙 _ :=
    (SSet.HomotopyCategory.homMk_comp_homMk d.inverseLeft).trans
      (SSet.HomotopyCategory.homMk_id _)
  have htri : SSet.HomotopyCategory.homMk d.inverse ≫
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy K) =
      SSet.HomotopyCategory.homMk d.edge :=
    SSet.HomotopyCategory.homMk_comp_homMk d.triangle
  rw [← htri, ← Category.assoc, hinv, Category.id_comp]

/-- 元の二列を比較する。両列が空なら、全時刻で定数の実比較を選ぶ。 -/
def familyCorrectionSpanData {U E : SSet.{u}} [KanComplex E] {s a b : U ⟶ E}
    (c : FamilyHomotopyChain s a) (d : FamilyHomotopyChain s b) :
    FamilyCorrectionSpanData (familyChainCompositeData c).homotopy
      (familyChainCompositeData d).homotopy := by
  cases c with
  | nil s =>
      cases d with
      | nil =>
          refine ⟨_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl s, SSet.Edge.CompStruct.ofTruncated
            (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.compStruct_nonempty_of_homMk_fac ?_).some⟩
          change SSet.Truncated.HomotopyCategory.homMk
              (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl s)) ≫
            SSet.Truncated.HomotopyCategory.homMk
              (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl s)) =
            SSet.Truncated.HomotopyCategory.homMk
              (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl s))
          rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl_hom]
          exact Category.comp_id _
      | cons K rest => exact familySpanComparisonData _ _
  | cons H tail => exact familySpanComparisonData _ _

/-- 二つの元の全補正列が空なら、実比較円柱全体が元の始点族で定数。 -/
lemma familyCorrectionSpanData_constant {U E : SSet.{u}} [KanComplex E] {s a b : U ⟶ E}
    (c : FamilyHomotopyChain s a) (d : FamilyHomotopyChain s b)
    (hc : familyHomotopyChainTrace c = []) (hd : familyHomotopyChainTrace d = []) :
    (familyCorrectionSpanData c d).homotopy.h = fst U (Δ[1] : SSet.{u}) ≫ s := by
  cases c with
  | nil s =>
      cases d with
      | nil => rfl
      | cons K rest => cases hd
  | cons H tail => cases hc

/-- 空の二列の比較を、同じ実三角形を保ちつつ明示的な定数円柱として表示する。 -/
def familyCorrectionSpanDataOfEmpty {U E : SSet.{u}} [KanComplex E] {s a b : U ⟶ E}
    (c : FamilyHomotopyChain s a) (d : FamilyHomotopyChain s b)
    (hc : familyHomotopyChainTrace c = []) (hd : familyHomotopyChainTrace d = []) :
    FamilyCorrectionSpanData (familyChainCompositeData c).homotopy
      (familyChainCompositeData d).homotopy := by
  let D := familyCorrectionSpanData c d
  let V : SSet.Homotopy a b := {
    h := fst U (Δ[1] : SSet.{u}) ≫ s
    h₀ := by
      change SSet.ι₀ ≫ fst U (Δ[1] : SSet.{u}) ≫ s = a
      rw [SSet.ι₀_fst_assoc]
      exact familyHomotopyChain_eq_of_trace_nil c hc
    h₁ := by
      change SSet.ι₁ ≫ fst U (Δ[1] : SSet.{u}) ≫ s = b
      rw [SSet.ι₁_fst_assoc]
      exact familyHomotopyChain_eq_of_trace_nil d hd
    rel := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro x
      exact False.elim x.1.property }
  refine ⟨V, D.triangle.ofEq rfl ?_ rfl⟩
  change SSet.yonedaEquiv (curry D.homotopy.h) = SSet.yonedaEquiv (curry V.h)
  rw [familyCorrectionSpanData_constant c d hc hd]

end SerrePositivity.KST.SConstruction
