module
public import SerrePositivity.InfinityCategories.Stable.SquareFixedSpanCocone
public import SerrePositivity.InfinityCategories.Core.ColimitCoconeFamily

/-!
概要：固定 span の余錐比較から suspension の普遍四角形と厳密切断を構成する。
方針：実 fiber の同型で始対象性を余極限性へ戻し、全境界持ち上げを使う。
規約：安定性・有限余極限は仮定しない。使われ方：一般安定性判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 同じ固定 span の普遍性と suspension の全単体構成。 -/
lemma hasColimit_zeroOuterSpan_of_loopEquivalence {X : SSet.{u}} [Quasicategory X]
    [HasZeroVertex X] [HasFiniteLimits X]
    (s : X ⟶ loopDiagrams X) (hs : s ≫ loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation X 0 0))
    (p : (horn 2 0 : SSet.{u}) ⟶ X)
    (hp : IsZeroOuterSpanVertex (functorVertex p)) : HasColimit p := by
  let b : (zeroOuterSpans X) _⦋0⦌ := ⟨functorVertex p, by
    intro α
    have hα : α = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    rw [hα, op_id, CategoryTheory.Functor.map_id_apply]
    exact hp⟩
  let x := (zeroOuterSpanSource X).app (Opposite.op ⦋0⦌) b
  let b' : (vertexFiber (zeroOuterSpanSource X) x) _⦋0⦌ :=
    ⟨b, by rw [pinchedConstant_zero]⟩
  obtain ⟨v, hv⟩ := zeroCornerSquareFixedSpanFiber_hasInitial s hs hΩ x b'
  let e := zeroCornerSquareFixedSpanRawIso X b ≪≫ squareFixedSpanCoconeIso p
  let w := e.hom.app (Opposite.op ⦋0⦌) v
  have hw : IsInitialVertex w := hv.map_of_isIso e.hom
  let c := (coconeFamilyVertexEquiv p).symm w
  refine ⟨c, (isColimitCone_iff_isInitialVertex_coconeFamily c).mpr ?_⟩
  change IsInitialVertex ((coconeFamilyVertexEquiv p) ((coconeFamilyVertexEquiv p).symm w))
  rw [Equiv.apply_symm_apply]
  exact hw
end SerrePositivity.InfinityCategories
