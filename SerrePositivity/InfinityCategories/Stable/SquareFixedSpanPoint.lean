module
public import SerrePositivity.InfinityCategories.Stable.SquareFixedSpanCocone

/-!
概要：元の loop 四角形の押し出し性と、全 suspension/loop 図式の比較。
方針：同じ指定点の始対象性を実固定 span へ戻し、全図式の評価を比較する。
規約：安定性は仮定しない。使われ方：HA 1.4.2.27 の一般安定性判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 同じ実四角形と全単体の図式を保つ普遍性の比較。 -/
def squareFixedSpanVertex {X : SSet.{u}} (F : Δ[1] ⊗ Δ[1] ⟶ X) :
    (vertexFiber ((pre spanSquareBoundary).app X) (functorVertex (pushoutSpan F))) _⦋0⦌ :=
  ⟨functorVertex F, by
    change functorVertex (pushoutSpan F) = PinchedHom.constant _ 0
    rw [pinchedConstant_zero]⟩

/-- 同じ実四角形と全単体の図式を保つ普遍性の比較。 -/
lemma squareFixedSpanCoconeIso_vertex {X : SSet.{u}} (F : Δ[1] ⊗ Δ[1] ⟶ X) :
    (squareFixedSpanCoconeIso (pushoutSpan F)).hom.app (Opposite.op ⦋0⦌)
      (squareFixedSpanVertex F) =
    coconeFamilyVertexEquiv (pushoutSpan F) (pushoutCocone F) := by
  apply Subtype.ext
  rfl

/-- 同じ実四角形と全単体の図式を保つ普遍性の比較。 -/
lemma squareFixedSpanVertex_isInitial_iff {X : SSet.{u}} [Quasicategory X]
    (F : Δ[1] ⊗ Δ[1] ⟶ X) :
    IsInitialVertex (squareFixedSpanVertex F) ↔ IsPushoutSquare F := by
  have : Quasicategory
      (vertexFiber ((pre spanSquareBoundary).app X) (functorVertex (pushoutSpan F))) :=
    quasicategory_of_innerFibration (squareFixedSpanCoconeIso (pushoutSpan F)).hom
  let e := qCatEquivalenceOfIso (squareFixedSpanCoconeIso (pushoutSpan F))
  have h := e.isInitialVertex_iff (squareFixedSpanVertex F)
  change IsInitialVertex (squareFixedSpanVertex F) ↔
    IsInitialVertex ((squareFixedSpanCoconeIso (pushoutSpan F)).hom.app
      (Opposite.op ⦋0⦌) (squareFixedSpanVertex F)) at h
  rw [squareFixedSpanCoconeIso_vertex] at h
  exact h.trans (isColimitCone_iff_isInitialVertex_coconeFamily (pushoutCocone F)).symm

/-- 同じ実四角形と全単体の図式を保つ普遍性の比較。 -/
lemma squareFixedSpan_isPushout_of_initial {X : SSet.{u}} [Quasicategory X]
    {b : ((ihom (horn 2 0 : SSet.{u})).obj X) _⦋0⦌}
    (v : (vertexFiber ((pre spanSquareBoundary).app X) b) _⦋0⦌)
    (hv : IsInitialVertex v) (F : Δ[1] ⊗ Δ[1] ⟶ X)
    (hF : v.val = functorVertex F) : IsPushoutSquare F := by
  have hb : b = functorVertex (pushoutSpan F) := by
    exact (v.property.trans (pinchedConstant_zero b)).symm.trans
      (congrArg (((pre spanSquareBoundary).app X).app (Opposite.op ⦋0⦌)) hF)
  subst b
  have he : v = squareFixedSpanVertex F := Subtype.ext hF
  rw [he] at hv
  exact (squareFixedSpanVertex_isInitial_iff F).mp hv

end SerrePositivity.InfinityCategories
