module

public import SerrePositivity.InfinityCategories.HomotopyLimits.IntervalVertexHomotopy
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.RightIntervalEquivalence

/-!
概要：区間写像空間内の元の頂点同型から、回収した同じ辺の Hom 類の等式を反映する。
方針：右 pinched 模型の充満忠実性で同型を戻し、連結成分から元の Hom へ写す。
規約：元の二頂点と回収辺の全一単体を変更しない。
使われ方：native な標準余錐変換と選択済み単位の比較を、合成類の等式へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
open SSet.Truncated.HomotopyCategory

/-- 区間写像空間内で同型な元の二頂点から回収した辺は、元の Hom 内で同じ類。 -/
lemma intervalRecoveredHom_eq_of_vertexIso {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} {v w : (intervalMappingSpace x y) _⦋0⦌}
    (e : VertexIso (X := intervalMappingSpace x y) v w) :
    homMk (intervalMappingEdgeOfVertex v).toTruncated =
      homMk (intervalMappingEdgeOfVertex w).toTruncated := by
  let P (t : (intervalMappingSpace x y) _⦋0⦌) :=
    (pinchedHomVertexEquiv x y).symm (intervalMappingEdgeOfVertex t).toTruncated
  have hp (t : (intervalMappingSpace x y) _⦋0⦌) :
      (pinchedHomToIntervalMappingSpace x y).app (Opposite.op ⦋0⦌) (P t) = t := by
    rw [pinchedHomToIntervalMappingSpace_vertex]
    have he : pinchedHomVertexEquiv x y (P t) = (intervalMappingEdgeOfVertex t).toTruncated :=
      (pinchedHomVertexEquiv x y).apply_symm_apply _
    rw [he]
    exact (intervalMappingEdgeVertexEquiv x y).apply_symm_apply t
  let i : VertexIso (X := pinchedHom x y) (P v) (P w) :=
    (pinchedHomToIntervalMappingSpace_isQCatEquivalence x y).isFullyFaithful.preimageVertexIso
      (eqToIso (congrArg HomotopyCategory.mk (hp v)) ≪≫ e ≪≫
      eqToIso (congrArg HomotopyCategory.mk (hp w).symm))
  obtain ⟨a, _⟩ := homotopyCategory_homMk_surjective (P v) (P w) i.hom
  have h := congrArg (pinchedHomPiZeroToHom x y) (SSet.π₀.sound (SSet.Edge.ofTruncated a))
  change homMk (pinchedHomVertexEquiv x y (P v)) =
    homMk (pinchedHomVertexEquiv x y (P w)) at h
  simpa only [P, Equiv.apply_symm_apply] using h

end SerrePositivity.InfinityCategories.HomotopyLimits
