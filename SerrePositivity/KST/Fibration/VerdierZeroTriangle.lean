module

public import SerrePositivity.InfinityCategories.F1.MappingSpaces.MappingSpaceModelEquivalence
public import SerrePositivity.KST.Fibration.ZeroStableHom
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentTerminal
public import SerrePositivity.InfinityCategories.F1B.Cofinality.InitialMappingSpace
public import SerrePositivity.InfinityCategories.Stable.UniverseZeroObjects

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
theorem stableVertex_isTerminal_of_zeroCategory (Z : StableQCat.{u})
    (hZ : IsZeroCategory Z) : IsTerminalVertex (stableVertex Z) := by
  change IsTerminalVertex (coherentNerveVertex Z)
  apply isTerminalVertex_of_pinchedHom_isContractibleKan
  intro x
  obtain ⟨A, rfl⟩ := (coherentNerveVertexEquiv StableQCat.{u}).surjective x
  apply (coherentHomEquivalence A Z).isContractibleKan
  have h := stableHom_isContractibleKan_of_zeroTarget A Z hZ
  apply isContractibleKan_of_nonempty_of_all_terminal
  · exact h.nonempty.map ULift.up
  · rintro ⟨v⟩
    exact (isTerminalVertex_iff_ulift v).mp (h.isTerminalVertex v)

/-- 全対象が零の安定圏は、全完全関手の ∞ 圏でも始対象である。 -/
theorem stableVertex_isInitial_of_zeroCategory (Z : StableQCat.{u})
    (hZ : IsZeroCategory Z) : IsInitialVertex (stableVertex Z) := by
  change IsInitialVertex (coherentNerveVertex Z)
  apply isInitialVertex_of_pinchedHomLeft_isContractibleKan
  intro x
  obtain ⟨A, rfl⟩ := (coherentNerveVertexEquiv StableQCat.{u}).surjective x
  apply (pinchedHomLeftRightEquivalence _ _).symm.isContractibleKan
  apply (coherentHomEquivalence Z A).isContractibleKan
  have h := stableHom_isContractibleKan_of_zeroSource Z A hZ
  apply isContractibleKan_of_nonempty_of_all_terminal
  · exact h.nonempty.map ULift.up
  · rintro ⟨v⟩
    exact (isTerminalVertex_iff_ulift v).mp (h.isTerminalVertex v)

/-- 全対象が零の安定圏を表す元の頂点は、StableInfinity の実零頂点である。 -/
theorem stableVertex_isZero_of_zeroCategory (Z : StableQCat.{u}) (hZ : IsZeroCategory Z) :
    IsZeroVertex (stableVertex Z) :=
  ⟨stableVertex_isInitial_of_zeroCategory Z hZ,
    stableVertex_isTerminal_of_zeroCategory Z hZ⟩

/-- 零安定圏を値とする実零頂点の存在。必要な箇所でだけ局所 instance として使う。 -/
theorem stableInfinity_hasZeroVertex : HasZeroVertex StableInfinity.{u} :=
  ⟨⟨stableVertex zeroCategory, stableVertex_isZero_of_zeroCategory _ zeroCategory_isZero⟩⟩

/-- 指定した元の Verdier 四角形の角は、全写像空間によって実零対象と判定される。 -/
theorem verdierDiagram_corner_isZero (d : VerdierDiagram.{u}) :
    IsZeroVertex (squareVertex d.square 0 1) := by
  have hz := stableVertex_isZero_of_zeroCategory
    (stableObject (squareVertex d.square 0 1)) d.zero_corner
  exact stableVertex_object (squareVertex d.square 0 1) ▸ hz

/-- 元の四角形・辺・全二胞体を変更せず、指定した Verdier 零合成を保持する。 -/
def verdierDiagramZeroTriangle (d : VerdierDiagram.{u}) : ZeroTriangle StableInfinity.{u} where
  square := d.square
  zero_corner := verdierDiagram_corner_isZero d

end SerrePositivity.KST.Fibration
