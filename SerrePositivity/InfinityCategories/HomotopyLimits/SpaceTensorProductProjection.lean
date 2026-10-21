module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SpaceTensorProduct

/-!
概要：coherent な二項積の射影を元の Kan 複体の射影と照合する。
方針：同じ豊穣比較の辺を標準頂点で評価し、任意の図式に前合成する。
規約：射影の辺の代表を変更しない。使われ方：小さい全空間への積比較の入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- coherent な第一射影の成分は元の fst の辺そのもの。 -/
lemma spaceTensorProductFstHomotopy_component (K L : KanObject.{u}) :
    (simplicialHomotopyVertexEdge spaceTensorProductFstHomotopy
      (coherentNerveVertex K, coherentNerveVertex L)).edge =
        (coherentNerveEdge (kanTensorEnrichedFst.val (K, L))).edge := by
  let X : SimplicialPairObject KanObject.{u} KanObject.{u} := (K, L)
  let H := simplicialHomotopyOfFunctorEdge
    (kanEnrichedComparisonEdge kanTensorEnrichedFst).toTruncated
  have h := (evaluateFunctorAt_edge
    (kanEnrichedComparisonEdge kanTensorEnrichedFst).toTruncated
      (coherentNerveVertex X)).trans (kanEnrichedComparisonEdge_at kanTensorEnrichedFst X)
  have hc : (simplicialPairNerveFrom KanObject.{u} KanObject.{u}).app (Opposite.op ⦋1⦌)
      (PinchedHom.constant (coherentNerveVertex K, coherentNerveVertex L) 1) =
        PinchedHom.constant (coherentNerveVertex X) 1 :=
    (pinchedConstant_map _ _ _).trans
      (congrArg (fun v ↦ PinchedHom.constant v 1) (simplicialPairNerveFrom_vertex K L))
  change H.h.app (Opposite.op ⦋1⦌)
    ((simplicialPairNerveFrom KanObject.{u} KanObject.{u}).app (Opposite.op ⦋1⦌)
      (PinchedHom.constant (coherentNerveVertex K, coherentNerveVertex L) 1),
        homotopyIntervalEdge.edge) = _
  rw [hc]
  exact h

/-- coherent な第二射影の成分も元の snd の辺そのもの。 -/
lemma spaceTensorProductSndHomotopy_component (K L : KanObject.{u}) :
    (simplicialHomotopyVertexEdge spaceTensorProductSndHomotopy
      (coherentNerveVertex K, coherentNerveVertex L)).edge =
        (coherentNerveEdge (kanTensorEnrichedSnd.val (K, L))).edge := by
  let X : SimplicialPairObject KanObject.{u} KanObject.{u} := (K, L)
  let H := simplicialHomotopyOfFunctorEdge
    (kanEnrichedComparisonEdge kanTensorEnrichedSnd).toTruncated
  have h := (evaluateFunctorAt_edge
    (kanEnrichedComparisonEdge kanTensorEnrichedSnd).toTruncated
      (coherentNerveVertex X)).trans (kanEnrichedComparisonEdge_at kanTensorEnrichedSnd X)
  have hc : (simplicialPairNerveFrom KanObject.{u} KanObject.{u}).app (Opposite.op ⦋1⦌)
      (PinchedHom.constant (coherentNerveVertex K, coherentNerveVertex L) 1) =
        PinchedHom.constant (coherentNerveVertex X) 1 :=
    (pinchedConstant_map _ _ _).trans
      (congrArg (fun v ↦ PinchedHom.constant v 1) (simplicialPairNerveFrom_vertex K L))
  change H.h.app (Opposite.op ⦋1⦌)
    ((simplicialPairNerveFrom KanObject.{u} KanObject.{u}).app (Opposite.op ⦋1⦌)
      (PinchedHom.constant (coherentNerveVertex K, coherentNerveVertex L) 1),
        homotopyIntervalEdge.edge) = _
  rw [hc]
  exact h

/-- 任意の coherent な積図式から第一図式への指定変換。 -/
def coherentSpaceTensorProductFstHomotopy {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) : SSet.Homotopy (coherentSpaceTensorProduct F G) F := by
  let H := functorHomotopyPrecomp spaceTensorProductFstHomotopy (lift F G)
  exact { h := H.h, h₀ := H.h₀, h₁ := H.h₁.trans (lift_fst F G), rel := H.rel }

/-- 任意の coherent な積図式から第二図式への指定変換。 -/
def coherentSpaceTensorProductSndHomotopy {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) : SSet.Homotopy (coherentSpaceTensorProduct F G) G := by
  let H := functorHomotopyPrecomp spaceTensorProductSndHomotopy (lift F G)
  exact { h := H.h, h₀ := H.h₀, h₁ := H.h₁.trans (lift_snd F G), rel := H.rel }

end SerrePositivity.InfinityCategories.HomotopyLimits
