module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramLocalizedVertices

/-!
概要：元のstrict図式の局所化の頂点を、同じReedy cofibrant図式で表示する。
方針：同じ局所化の頂点表示に余単体的解像の零次増大を合成する。
規約：任意の局所化頂点が対象。cofibrancyを最終比較の追加入力にしない。
使われ方：HTT 4.2.4.4の写像空間の実frameの入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomotopicalAlgebra SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (d : StrictDiagramDirection)
local instance : ModelCategory (StrictComplexDiagram A d) := strictDiagramReedyModelCategory A d
local instance : CategoryTheory.Limits.HasInitial (StrictComplexDiagram A d) :=
  (CategoryTheory.Limits.isZero_zero (StrictComplexDiagram A d)).isInitial.hasInitial

/-- 任意の局所化頂点は、同じcofibrant図式の像と同型である。 -/
lemma exists_strictDiagramCofibrantVertex (x : (StrictDiagramInfinity A d) _⦋0⦌) :
    ∃ X : StrictComplexDiagram A d, IsCofibrant X ∧
      Nonempty (VertexIso
        ((strictDiagramLocalization A d).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ X)) x) := by
  obtain ⟨v, ⟨e⟩⟩ := strictDiagramLocalization_isEssentiallySurjective A d x
  obtain ⟨X, rfl⟩ := ComposableArrows.mk₀_surjective v
  let Q := strictDiagramSourceFrame A d X
  let X' := Q.obj.obj ⦋0⦌
  let a : X' ⟶ X := Q.augmentation.app ⦋0⦌
  have ha : strictDiagramQuasiIsos A d a := by
    rw [← strictDiagramReedyModelCategory_weakEquivalences]
    exact Q.augmentation_weakEquivalence _
  have hi := (strictDiagramLocalization_inverts A d)
    ((strictDiagramWeakEdges_mk₁ A d a).2 ha)
  change IsInvertibleEdge
    ((edgeOfSimplex (X := strictComplexDiagramNerve A d) (ComposableArrows.mk₁ a)).map
      ((truncation 2).map (strictDiagramLocalization A d))) at hi
  have hi' : IsInvertibleEdge
      (((nerve.edgeMk a).map (strictDiagramLocalization A d)).toTruncated) := by
    exact (isInvertibleEdge_congr
      (e := ((nerve.edgeMk a).map (strictDiagramLocalization A d)).toTruncated)
      (f := (edgeOfSimplex (X := strictComplexDiagramNerve A d) (ComposableArrows.mk₁ a)).map
        ((truncation 2).map (strictDiagramLocalization A d))) rfl).mpr hi
  haveI := hi'
  refine ⟨X', Q.isCofibrant_obj _, ⟨?_⟩⟩
  exact asIso (Truncated.HomotopyCategory.homMk
    (((nerve.edgeMk a).map (strictDiagramLocalization A d)).toTruncated)) ≪≫ e

/-- 元の頂点の、上の同じ存在証明から選ぶcofibrant図式。 -/
def strictDiagramCofibrantVertex (x : (StrictDiagramInfinity A d) _⦋0⦌) :
    StrictComplexDiagram A d := (exists_strictDiagramCofibrantVertex A d x).choose

/-- 選んだ同じ図式はReedy cofibrantである。 -/
lemma strictDiagramCofibrantVertex_isCofibrant (x : (StrictDiagramInfinity A d) _⦋0⦌) :
    IsCofibrant (strictDiagramCofibrantVertex A d x) :=
  (exists_strictDiagramCofibrantVertex A d x).choose_spec.1

/-- 同じ存在証明が返す、元の局所化頂点への指定同型。 -/
def strictDiagramCofibrantVertexIso (x : (StrictDiagramInfinity A d) _⦋0⦌) :
    VertexIso ((strictDiagramLocalization A d).app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ (strictDiagramCofibrantVertex A d x))) x :=
  (exists_strictDiagramCofibrantVertex A d x).choose_spec.2.some

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
