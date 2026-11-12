module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceModelEquivalence
public import SerrePositivity.KST.Fibration.ZeroStableHom
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.CoherentTerminal
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.InitialMappingSpace
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseZeroObjects

/-! # 指定 Verdier 四角形の零合成を、元の StableInfinity の零角付き四角形として保持する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 全対象が零の安定圏は、全完全関手の ∞ 圏でも終対象である。 -/
theorem stableVertex_isTerminal_of_zeroCategory (Z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u})
    (hZ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory Z) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex Z) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Z)
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isTerminalVertex_of_pinchedHom_isContractibleKan
  intro x
  obtain ⟨A, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertexEquiv _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}).surjective x
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomEquivalence A Z).isContractibleKan
  have h := stableHom_isContractibleKan_of_zeroTarget A Z hZ
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.isContractibleKan_of_nonempty_of_all_terminal
  · exact h.nonempty.map ULift.up
  · rintro ⟨v⟩
    exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isTerminalVertex_iff_ulift v).mp (h.isTerminalVertex v)

/-- 全対象が零の安定圏は、全完全関手の ∞ 圏でも始対象である。 -/
theorem stableVertex_isInitial_of_zeroCategory (Z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u})
    (hZ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory Z) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex Z) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Z)
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isInitialVertex_of_pinchedHomLeft_isContractibleKan
  intro x
  obtain ⟨A, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertexEquiv _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}).surjective x
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeftRightEquivalence _ _).symm.isContractibleKan
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomEquivalence Z A).isContractibleKan
  have h := stableHom_isContractibleKan_of_zeroSource Z A hZ
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.isContractibleKan_of_nonempty_of_all_terminal
  · exact h.nonempty.map ULift.up
  · rintro ⟨v⟩
    exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isTerminalVertex_iff_ulift v).mp (h.isTerminalVertex v)

/-- 全対象が零の安定圏を表す元の頂点は、StableInfinity の実零頂点である。 -/
theorem stableVertex_isZero_of_zeroCategory (Z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) (hZ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory Z) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex Z) :=
  ⟨stableVertex_isInitial_of_zeroCategory Z hZ,
    stableVertex_isTerminal_of_zeroCategory Z hZ⟩

/-- 零安定圏を値とする実零頂点の存在。必要な箇所でだけ局所 instance として使う。 -/
theorem stableInfinity_hasZeroVertex : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} :=
  ⟨⟨_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory, stableVertex_isZero_of_zeroCategory _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory_isZero⟩⟩

/-- 指定した元の Verdier 四角形の角は、全写像空間によって実零対象と判定される。 -/
theorem verdierDiagram_corner_isZero (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex d.square 0 1) := by
  have hz := stableVertex_isZero_of_zeroCategory
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex d.square 0 1)) d.zero_corner
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex_object (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex d.square 0 1) ▸ hz

/-- 元の四角形・辺・全二胞体を変更せず、指定した Verdier 零合成を保持する。 -/
def verdierDiagramZeroTriangle (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} where
  square := d.square
  zero_corner := verdierDiagram_corner_isZero d

end SerrePositivity.KST.Fibration
