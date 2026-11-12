module

public import SerrePositivity.KST.Spectra.SequenceRelativeTracedRectification

/-!
概要：実区間を保持する相対列厳密化から、同じ射影を固定する元の構造三角形を回収する。
方針：次段比較の制限を、帰納段の対角区間の同じ一次単体へ厳密に照合する。
規約：三角形の単体を変更しない。使われ方：相対比較の段方向の高次整合性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.KanSequence
variable {X Y Z : KanSequence.{u}} (hX : ∀ n, Mono (X.sigma n).right)
  (q : Hom Y Z) (hq : ∀ n, SSet.modelCategoryQuillen.J.rlp (q.app n).right)
  (b : Hom X Z) (f : ∀ n, (X.level n).space ⟶ (Y.level n).space)
  (hb : ∀ n, f n ≫ q.app n = b.app n)
  (h : ∀ n, PointedMapping.VerticalPath (q.app (n + 1))
    (X.sigma n ≫ f (n + 1)) (PointedSimplicialSet.circle.{u} ◁ f n ≫ Y.sigma n))

/-- 次段比較の制限の終点を、厳密可換式の同じ終点へ移す。 -/
def relativeTracedRestrictionPath (n : ℕ) :
    PointedMapping.VerticalPath (q.app (n + 1)) (X.sigma n ≫ f (n + 1))
      (PointedSimplicialSet.circle.{u} ◁ (relativeTracedRectify hX q hq b f hb h).app n ≫
        Y.sigma n) :=
  ((relativeTracedRectifyComparison hX q hq b f hb h (n + 1)).pre (X.sigma n)).changeEndpoints
    rfl ((relativeTracedRectify hX q hq b f hb h).comm n)

/-- 次段比較の制限は、同じ fiber 内で貼った対角区間の族そのもの。 -/
lemma relativeTracedRestrictionPath_path (n : ℕ) :
    (relativeTracedRestrictionPath hX q hq b f hb h n).path =
      (relativeTracedComposite q hq b f h n
        (relativeTracedStage hX q hq b f hb h n)).path.path := by
  apply PointedMapping.VerticalPath.path_eq_of_homotopy_h_eq
  rw [relativeTracedRestrictionPath, PointedMapping.VerticalPath.changeEndpoints_homotopy_h,
    PointedMapping.VerticalPath.pre_homotopy_h]
  exact relativeTracedRectifyComparison_restriction hX q hq b f hb h n

/-- 元の対角区間の辺も、同じ一次単体として厳密に一致する。 -/
lemma relativeTracedRestrictionPath_edge (n : ℕ) :
    (relativeTracedRestrictionPath hX q hq b f hb h n).edge =
      (relativeTracedComposite q hq b f h n
        (relativeTracedStage hX q hq b f hb h n)).path.edge := by
  apply SSet.Edge.ext
  change SSet.yonedaEquiv _ = SSet.yonedaEquiv _
  rw [relativeTracedRestrictionPath_path]

/-- 元の構造区間・前段修正・次段修正の制限を三辺に持つ、同じ相対構造三角形。 -/
def relativeTracedComparison_triangle (n : ℕ) :
    SSet.Edge.CompStruct (h n).edge
      (relativeTracedStepPath q b f n (relativeTracedStage hX q hq b f hb h n)).edge
      (relativeTracedRestrictionPath hX q hq b f hb h n).edge := by
  let t := (relativeTracedComposite q hq b f h n
    (relativeTracedStage hX q hq b f hb h n)).triangle
  have he := congrArg SSet.Edge.edge (relativeTracedRestrictionPath_edge hX q hq b f hb h n)
  exact { simplex := t.simplex, d₂ := t.d₂, d₀ := t.d₀, d₁ := t.d₁.trans he.symm }

/-- 回収した三角形の二次元単体は、元の fiber 内の合成三角形と同じ。 -/
lemma relativeTracedComparison_triangle_simplex (n : ℕ) :
    (relativeTracedComparison_triangle hX q hq b f hb h n).simplex =
      (relativeTracedComposite q hq b f h n
        (relativeTracedStage hX q hq b f hb h n)).triangle.simplex := rfl

/-- 三角形全体の射影も、元の指定した列の同じ構造射で一定。 -/
lemma relativeTracedComparison_triangle_over (n : ℕ) :
    SSet.yonedaEquiv.symm (relativeTracedComparison_triangle hX q hq b f hb h n).simplex ≫
      (PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) (q.app (n + 1))).right =
        SSet.const (PointedMapping.familyVertex (X.sigma n ≫ b.app (n + 1))) := by
  rw [relativeTracedComparison_triangle_simplex]
  have hc := (relativeTracedComposite q hq b f h n
    (relativeTracedStage hX q hq b f hb h n)).triangle_over
  rw [Category.assoc, hb (n + 1)] at hc
  exact hc

end SerrePositivity.KST.Spectra.KanSequence
