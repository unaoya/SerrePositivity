module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromCategoriesToSimplicialSets.KanCharacterization

/-! # 元の二辺を保持する Kan 写像空間の span の合成
概要：共通の始点を持つ二辺を、指定した逆の三角形と合成三角形を保持して一本の辺にする。
方針：第一辺の逆を両逆三角形付きで取り、第二辺と指定した三辺で合成する。
規約：元の二辺を変更せず、選択した証人を全て実三角形として保存する。
使われ方：自然性 square から復号した二辺を、元の適合ホモトピーへ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial

/-- 元の span の第一辺の両逆証人と、元の第二辺との実合成三角形。 -/
structure KanMappingSpanComposition {E : SSet.{u}} {z x y : E _⦋0⦌}
    (a : E.Edge z x) (b : E.Edge z y) where
  /-- 第一辺の選んだ逆辺。 -/
  inverse : E.Edge x z
  /-- 第一辺と逆辺を合成する元の左逆三角形。 -/
  inverseLeft : SSet.Edge.CompStruct a inverse (SSet.Edge.id z)
  /-- 逆辺と第一辺を合成する元の右逆三角形。 -/
  inverseRight : SSet.Edge.CompStruct inverse a (SSet.Edge.id x)
  /-- span から得た実際の合成辺。 -/
  edge : E.Edge x y
  /-- 元の逆辺・元の第二辺・合成辺を保持する実三角形。 -/
  triangle : SSet.Edge.CompStruct inverse b edge

/-- 元の二辺を保持し、全ての証人を実三角形として伴う span の合成。 -/
def kanMappingSpanComposition {E : SSet.{u}} [KanComplex E] {z x y : E _⦋0⦌}
    (a : E.Edge z x) (b : E.Edge z y) : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanMappingSpanComposition a b := by
  have ha : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge a.toTruncated :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.isInvertibleEdge_of_hasFinalHornFillers _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.hasFinalHornFillers_of_kanComplex _)
  let invData := ha.nonempty_inverse.some
  let inv := SSet.Edge.ofTruncated invData.1
  have hex := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective x y
    (SSet.Truncated.HomotopyCategory.homMk inv.toTruncated ≫
      SSet.Truncated.HomotopyCategory.homMk b.toTruncated)
  let e := SSet.Edge.ofTruncated hex.choose
  let ht := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.compStruct_nonempty_of_homMk_fac hex.choose_spec.symm
  exact ⟨inv, SSet.Edge.CompStruct.ofTruncated invData.2.1,
    SSet.Edge.CompStruct.ofTruncated invData.2.2, e, SSet.Edge.CompStruct.ofTruncated ht.some⟩

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
