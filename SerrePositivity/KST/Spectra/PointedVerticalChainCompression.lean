module

public import SerrePositivity.KST.Spectra.PointedVerticalPathFiber
public import SerrePositivity.KST.Spectra.PostMappingFibration

/-!
概要：Kan fibration の上の垂直な有限鎖を、同じ射影を保持する単一の点つき区間へ戻す。
方針：元の内部 Hom の実際の Kan fiber で成分の等式を辺へ戻し、包含して評価する。
規約：全空間・底・パラメータの Kan 性は不要。使われ方：相対厳密化の修正鎖の回収。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet HomotopicalAlgebra
open scoped Simplicial
open SSet.modelCategoryQuillen
namespace SerrePositivity.KST.Spectra.PointedMapping.VerticalChain
variable {T E B : PointedSimplicialSet.{u}} {p : E ⟶ B} {f g : T ⟶ E}

/-- 垂直な有限鎖は、元の射影を全区間で保持する単一の点つき区間を持つ。 -/
lemma nonempty_path (H : VerticalChain p f g) (hp : J.rlp p.right) :
    Nonempty (VerticalPath p f g) := by
  let pFibration : Fibration p.right := (fibration_iff _).2 hp
  let postFibration : Fibration (PointedObject.basedHomMap T p).right :=
    PointedMapping.post_fibration T p
  let fiberKan : KanComplex (verticalFiber p f) := inferInstance
  obtain ⟨e⟩ := nonempty_edge_of_piZero_eq (H.fiber_component f rfl)
  exact ⟨VerticalPath.ofFiberEdge p f f g rfl H.endpoint_over e⟩

/-- 同じ Kan fiber 内で向きを戻しても、元の射影を全区間で保持する。 -/
lemma nonempty_reverse_path (H : VerticalChain p f g) (hp : J.rlp p.right) :
    Nonempty (VerticalPath p g f) := by
  let pFibration : Fibration p.right := (fibration_iff _).2 hp
  let postFibration : Fibration (PointedObject.basedHomMap T p).right :=
    PointedMapping.post_fibration T p
  let fiberKan : KanComplex (verticalFiber p g) := inferInstance
  have hc := (H.fiber_component g H.endpoint_over.symm).symm
  obtain ⟨e⟩ := nonempty_edge_of_piZero_eq hc
  exact ⟨VerticalPath.ofFiberEdge p g g f rfl H.endpoint_over.symm e⟩

/-- 有限鎖から回収した実際のホモトピーは、基点と元の射影を全区間で固定する。 -/
lemma exists_vertical_homotopy (H : VerticalChain p f g) (hp : J.rlp p.right) :
    ∃ V : SSet.Homotopy f.right g.right,
      T.hom ▷ (Δ[1] : SSet.{u}) ≫ V.h =
        toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫ E.hom ∧
      V.h ≫ p.right = fst T.right (Δ[1] : SSet.{u}) ≫ f.right ≫ p.right := by
  obtain ⟨P⟩ := H.nonempty_path hp
  exact ⟨P.homotopy, P.homotopy_base, P.homotopy_over⟩

end SerrePositivity.KST.Spectra.PointedMapping.VerticalChain
