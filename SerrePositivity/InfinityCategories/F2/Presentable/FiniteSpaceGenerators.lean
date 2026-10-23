module

public import SerrePositivity.InfinityCategories.F2.Presentable.FiniteSimplicialCodes
public import SerrePositivity.InfinityCategories.F2.Presentable.FiniteSpacePresentation
public import SerrePositivity.InfinityCategories.F2.Presentable.SmallFamilyGeneratorTransport

/-!
概要：共通の小さい有限コードから compact な空間族を作り、元の有限模型の全表示をこの族へ比較する。
方針：元の単体集合の同型に同じ連続 Kan 置換を施し、元の空間内の頂点同型へ移す。
規約：全表示の各有限部分を保持。compact 性を仮定しない。
使われ方：空間の小さい compact 生成圏と presentable 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 同じ小さい有限コード族を元の空間 ∞ 圏の compact な頂点族へ実現する。 -/
def finiteSpaceGeneratorVertex (q : FiniteSimplicialCode.{u}) : SpaceInfinity.{u} _⦋0⦌ :=
  coherentNerveVertex (continuousReplacementKanObject q.realization)

/-- 共通の小さい族の全項は、元の全 Hom の定義によって compact。 -/
lemma finiteSpaceGeneratorVertex_isCompact (q : FiniteSimplicialCode.{u}) :
    Compact.IsKappaCompact.{u, u + 1} Cardinal.aleph0 (finiteSpaceGeneratorVertex q) :=
  finiteKanReplacement_isCompact q.realization

/-- 元の単体集合の同型を、同じ Kan 置換の元の空間内の頂点同型へ移す。 -/
def continuousReplacementVertexIso {A B : SSet.{u}} (e : A ≅ B) :
    VertexIso (coherentNerveVertex (continuousReplacementKanObject A))
      (coherentNerveVertex (continuousReplacementKanObject B)) := by
  let f : continuousReplacementKanObject A ⟶ continuousReplacementKanObject B :=
    continuousKanReplacement.map e.hom
  have hf : IsQCatEquivalence f :=
    (qCatEquivalenceOfIso (continuousKanReplacement.mapIso e)).isQCatEquivalence
  have he := coherentKanEdge_isInvertible_of_isQCatEquivalence hf
  have : IsIso (SSet.Truncated.HomotopyCategory.homMk (coherentNerveEdge f).toTruncated) := he
  exact asIso (SSet.Truncated.HomotopyCategory.homMk (coherentNerveEdge f).toTruncated)

/-- 元の各有限模型の Kan 置換は、共通の小さい compact 族の一つと頂点同型を持つ。 -/
lemma exists_finiteSpaceGeneratorIso (A : SSet.{u}) [A.Finite] :
    FamilySaturation finiteSpaceGeneratorVertex
      (coherentNerveVertex (continuousReplacementKanObject A)) := by
  obtain ⟨q, ⟨e⟩⟩ := exists_finiteSimplicialCode A
  exact ⟨q, ⟨continuousReplacementVertexIso e.symm⟩⟩

/-- 元の全表示の全項は、同じ共通の小さい compact 族の同型飽和に属する。 -/
lemma finiteSpaceReplacementDiagram_in_family (X : SSet.{u})
    (a : (nerve (FiniteSpacePieces X)) _⦋0⦌) :
    FamilySaturation finiteSpaceGeneratorVertex
      ((strictCoherentDiagram (finiteSpaceReplacementDiagram X)).app _ (ULift.up a)) := by
  obtain ⟨A, rfl⟩ := nerveEquiv.symm.surjective a
  change FamilySaturation finiteSpaceGeneratorVertex
    ((strictCoherentDiagram (finiteSpaceReplacementDiagram X)).app _ (ULift.up (nerveVertex A)))
  rw [strictCoherentDiagram_eq_kanDiagram]
  erw [kanDiagramCoherentNerve_vertex, spaceInfinityVertex_eq_coherent]
  exact exists_finiteSpaceGeneratorIso A.val.toSSet

end SerrePositivity.InfinityCategories.F2.Presentable
