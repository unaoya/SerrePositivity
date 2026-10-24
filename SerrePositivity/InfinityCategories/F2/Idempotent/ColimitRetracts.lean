module

public import SerrePositivity.InfinityCategories.F2.Idempotent.RelativeInitialComplete
public import SerrePositivity.InfinityCategories.F2.Idempotent.CompleteImageRetracts
public import SerrePositivity.InfinityCategories.Core.ColimitDiagramIso

/-!
概要：冪等完備な元の ∞ 圏では、全関手 ∞ 圏内の元の図式の retract も余極限を持つ。
方針：全普遍余錐の冪等完備性と、元の射影の充満忠実な像の retract 閉性を使う。
規約：任意の添字・全図式を扱い、独立な頂点ごとの retract では代用しない。
使われ方：完備化の新しい辺の cofiber の存在を元の普遍図式から得る。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 冪等完備な元の圏内で、余極限を持つ全図式の元の retract も余極限を持つ。 -/
lemma hasColimit_of_diagram_retract {K X : SSet.{u}} [Quasicategory X]
    (hX : IsIdempotentComplete X) (a b : K ⟶ X)
    (r : VertexRetraction (functorVertex a) (functorVertex b)) (hb : HasColimit b) :
    HasColimit a := by
  obtain ⟨c, hc⟩ := hb
  let v : (colimitCocones K X) _⦋0⦌ := ⟨functorVertex c.val, by
    intro α
    have hα : α = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    rw [hα, op_id, Functor.map_id_apply]
    exact hc.initialBoundaryLifting⟩
  let q := colimitCoconeProjection K X
  have hqv : q.app (Opposite.op ⦋0⦌) v = functorVertex b := by
    change functorVertex (joinInl K Δ[0] ≫ c.val) = _
    rw [c.property]
  obtain ⟨w, ⟨e⟩⟩ := IsIdempotentComplete.retract_iso_in_image
    (colimitCocones_isIdempotentComplete K hX) q (colimitCoconeProjection_isFullyFaithful K X)
    v (functorVertex a) (by rw [hqv]; exact r)
  let F := (functorVertexEquiv (join K (Δ[0] : SSet.{u})) X).symm w.val
  have hF : functorVertex F = w.val := (functorVertexEquiv _ _).apply_symm_apply _
  let d : JoinCocone (joinInl K Δ[0] ≫ F) := ⟨F, rfl⟩
  have hd : IsColimitCone d := by
    apply (colimitCocones_vertex_iff d).mp
    change InitialBoundaryLifting (coconeRestriction K X) (functorVertex F)
    rw [hF]
    exact fullSubcomplexOnVertices_vertex w
  have hw : q.app (Opposite.op ⦋0⦌) w = functorVertex (joinInl K Δ[0] ≫ F) := by
    change (coconeRestriction K X).app (Opposite.op ⦋0⦌) w.val = _
    rw [← hF]
    rfl
  have ei : FunctorIso a (joinInl K Δ[0] ≫ F) := by
    change VertexIso (functorVertex a) (functorVertex (joinInl K Δ[0] ≫ F))
    exact hw ▸ e
  exact (hasColimit_iff_of_functorIso ei).mpr ⟨d, hd⟩

end SerrePositivity.InfinityCategories.F2.Idempotent
