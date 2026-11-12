module
public import SerrePositivity.KST.SConstruction.FamilyChainCompositionWitness

/-! # 全合成証人付きの有限補正列の実比較円柱
概要：Kan 標的で元の有限列を一本の実円柱へ合成し、元の全区間と全三角形を保存する。
方針：内部 Hom 内で元の二辺を実合成し、円柱への復号後も同じ三面を保持する。
規約：各段の元の区間・合成木を結果に含め、存在を追加仮定にしない。
使われ方：各段の元の補正有限列から raw 比較円柱を内部構成する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 元の有限列の一本の実比較円柱と、全区間・全合成三角形の証人。 -/
structure FamilyChainCompositeData {U E : SSet.{u}} {f g : U ⟶ E}
    (c : FamilyHomotopyChain f g) where
  /-- 同じ両端を持つ一本の実円柱。 -/
  homotopy : SSet.Homotopy f g
  /-- 元の全区間と全二単体の合成木。 -/
  witness : FamilyChainCompositionWitness c homotopy

/-- Kan 標的で、元の全区間の記録を保つ実比較円柱を構成する。 -/
def familyChainCompositeData {U E : SSet.{u}} [KanComplex E] {f g : U ⟶ E}
    (c : FamilyHomotopyChain f g) : FamilyChainCompositeData c := by
  induction c with
  | nil f => exact ⟨_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl f, .nil f⟩
  | cons a tail T =>
      let d := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.kanMappingComposition
        (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy a))
        (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy T.homotopy))
      let H := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge d.edge.toTruncated
      have he : (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)).edge = d.edge.edge := by
        change SSet.yonedaEquiv (curry (uncurry (SSet.yonedaEquiv.symm d.edge.edge))) = _
        rw [curry_uncurry, Equiv.apply_symm_apply]
      exact ⟨H, .cons a tail T.witness (d.triangle.ofEq rfl rfl he.symm)⟩

/-- 合成後も元の全入力区間と順序を厳密に回収する。 -/
lemma familyChainCompositeData_trace {U E : SSet.{u}} [KanComplex E] {f g : U ⟶ E}
    (c : FamilyHomotopyChain f g) :
    familyChainCompositionInputTrace (familyChainCompositeData c).witness =
      familyHomotopyChainTrace c := familyChainCompositionInputTrace_eq _

/-- 元の区間が空なら、合成円柱は元の始点族の全時刻での定数円柱。 -/
lemma familyChainCompositionWitness_constant_of_trace_nil {U E : SSet.{u}} {f g : U ⟶ E}
    {c : FamilyHomotopyChain f g} {H : SSet.Homotopy f g}
    (w : FamilyChainCompositionWitness c H) (hc : familyHomotopyChainTrace c = []) :
    H.h = CartesianMonoidalCategory.fst U (Δ[1] : SSet.{u}) ≫ f := by
  cases w with
  | nil => rfl
  | cons a tail tailWitness triangle => cases hc

/-- 空の補正列には、実比較円柱の非定数な区間を追加しない。 -/
lemma familyChainCompositeData_constant_of_trace_nil {U E : SSet.{u}} [KanComplex E]
    {f g : U ⟶ E} (c : FamilyHomotopyChain f g) (hc : familyHomotopyChainTrace c = []) :
    (familyChainCompositeData c).homotopy.h =
      CartesianMonoidalCategory.fst U (Δ[1] : SSet.{u}) ≫ f :=
  familyChainCompositionWitness_constant_of_trace_nil (familyChainCompositeData c).witness hc

end SerrePositivity.KST.SConstruction
