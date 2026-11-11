module

public import SerrePositivity.KST.Spectra.SequenceRelativeTracedTriangles
public import SerrePositivity.KST.Spectra.CompositionTriangleSquareProjection
public import SerrePositivity.KST.Spectra.IdentityTriangleHomotopy

/-!
概要：相対厳密化の元の構造三角形から、比較区間の段間の実正方形を回収する。
方針：同じ二単体を退化三角形と貼り、対角区間から前段比較の構造像へ移す。
規約：元の構造区間を始点境界に保持。使われ方：両端固定の構造区間への貼り合わせ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.KanSequence
variable {X Y Z : KanSequence.{u}} (hX : ∀ n, Mono (X.sigma n).right)
  (q : Hom Y Z) (hq : ∀ n, SSet.modelCategoryQuillen.J.rlp (q.app n).right)
  (b : Hom X Z) (f : ∀ n, (X.level n).space ⟶ (Y.level n).space)
  (hb : ∀ n, f n ≫ q.app n = b.app n)
  (h : ∀ n, PointedMapping.VerticalPath (q.app (n + 1))
    (X.sigma n ≫ f (n + 1)) (PointedSimplicialSet.circle.{u} ◁ f n ≫ Y.sigma n))


/-- 次段比較の制限から前段比較の構造像への、元の実三角形による正方形ホモトピー。 -/
def relativeTracedComparison_homotopy (n : ℕ) :
    SSet.Homotopy (relativeTracedRestrictionPath hX q hq b f hb h n).path
      (relativeTracedStepPath q b f n (relativeTracedStage hX q hq b f hb h n)).path where
  h := compositionTriangleSquare (relativeTracedComparison_triangle hX q hq b f hb h n)
  h₀ := by
    rw [compositionTriangleSquare_zero]
    exact Equiv.symm_apply_apply _ _
  h₁ := by
    rw [compositionTriangleSquare_one]
    exact Equiv.symm_apply_apply _ _
  rel := by ext m ⟨⟨s, hs⟩, r⟩; exact hs.elim

/-- 正方形の始点境界は、入力した元の構造区間そのもの。 -/
lemma relativeTracedComparison_homotopy_start (n : ℕ) :
    stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u}) ≫
        (relativeTracedComparison_homotopy hX q hq b f hb h n).h =
      snd (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ (h n).path := by
  change _ ≫ compositionTriangleSquare
    (relativeTracedComparison_triangle hX q hq b f hb h n) = _
  rw [compositionTriangleSquare_start]
  exact congrArg (_ ≫ ·) (Equiv.symm_apply_apply _ _)

/-- 正方形全体も、元の指定された列の同じ構造射へ定数で射影される。 -/
lemma relativeTracedComparison_homotopy_over (n : ℕ) :
    (relativeTracedComparison_homotopy hX q hq b f hb h n).h ≫
      (PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) (q.app (n + 1))).right =
        SSet.const (PointedMapping.familyVertex (X.sigma n ≫ b.app (n + 1))) :=
  compositionTriangleSquare_post_const _ _ _
    (relativeTracedComparison_triangle_over hX q hq b f hb h n)

/-- 元の構造区間が定数なら、同じ実正方形は区間の両端を全体で固定する。 -/
lemma relativeTracedComparison_homotopy_boundary (n : ℕ)
    (hh : (h n).path = SSet.const (PointedMapping.familyVertex (X.sigma n ≫ f (n + 1)))) :
    (boundary 1).ι ▷ (Δ[1] : SSet.{u}) ≫
        (relativeTracedComparison_homotopy hX q hq b f hb h n).h =
      fst (∂Δ[1] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ (boundary 1).ι ≫
        (relativeTracedRestrictionPath hX q hq b f hb h n).path := by
  have ht := compositionTriangleHomotopy_boundary_of_const
    (relativeTracedComparison_triangle hX q hq b f hb h n)
    ((Equiv.symm_apply_apply _ _).trans hh)
  exact ht.trans (congrArg (fst (∂Δ[1] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ (boundary 1).ι ≫ ·)
    (Equiv.symm_apply_apply _ _))

end SerrePositivity.KST.Spectra.KanSequence
