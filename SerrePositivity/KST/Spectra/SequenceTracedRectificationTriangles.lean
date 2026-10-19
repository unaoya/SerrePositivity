module

public import SerrePositivity.KST.Spectra.SequenceTracedRectification

/-!
概要：比較区間を保持する列の厳密化から、次段の制限を対角辺とする実構造三角形を回収する。
方針：延長で保持した全区間の等式を内部 Hom の同じ辺の等式へ戻す。
規約：成分の一致から三角形を選び直さない。使われ方：境界トレース恒等性の証明。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.KanSequence
variable {X Y : KanSequence.{u}} (hX : ∀ n, Mono (X.sigma n).right)
  (f : ∀ n, (X.level n).space ⟶ (Y.level n).space)
  (h : ∀ n, PointedMapping.VerticalPath (PointedObject.toPoint (Y.level (n + 1)).space)
    (X.sigma n ≫ f (n + 1)) (PointedSimplicialSet.circle.{u} ◁ f n ≫ Y.sigma n))

/-- 次段比較の制限の終点を、厳密な構造可換式の同じ終点に直す。 -/
def tracedRectifyRestrictionPath (n : ℕ) :
    PointedMapping.VerticalPath (PointedObject.toPoint (Y.level (n + 1)).space)
      (X.sigma n ≫ f (n + 1))
      (PointedSimplicialSet.circle.{u} ◁ (tracedRectify hX f h).app n ≫ Y.sigma n) :=
  ((tracedRectifyComparison hX f h (n + 1)).pre (X.sigma n)).changeEndpoints rfl
    ((tracedRectify hX f h).comm n)

/-- 次段の制限の元の区間族は、帰納段で貼った対角区間の族そのもの。 -/
lemma tracedRectifyRestrictionPath_path (n : ℕ) :
    (tracedRectifyRestrictionPath hX f h n).path =
      (tracedRectificationComposite f h n (tracedRectificationStage hX f h n)).path.path := by
  apply PointedMapping.VerticalPath.path_eq_of_homotopy_h_eq
  rw [tracedRectifyRestrictionPath, PointedMapping.VerticalPath.changeEndpoints_homotopy_h,
    PointedMapping.VerticalPath.pre_homotopy_h]
  exact tracedRectifyComparison_restriction hX f h n

/-- 同じ対角区間の辺への照合も、元の一次単体の厳密な等式。 -/
lemma tracedRectifyRestrictionPath_edge (n : ℕ) :
    (tracedRectifyRestrictionPath hX f h n).edge =
      (tracedRectificationComposite f h n (tracedRectificationStage hX f h n)).path.edge := by
  apply SSet.Edge.ext
  change SSet.yonedaEquiv _ = SSet.yonedaEquiv _
  rw [tracedRectifyRestrictionPath_path]

/-- 元の構造区間・前段修正・次段修正の制限を三辺に持つ、帰納段の同じ実三角形。 -/
def tracedRectifyComparison_triangle (n : ℕ) :
    SSet.Edge.CompStruct (h n).edge
      (tracedRectificationStepPath f n (tracedRectificationStage hX f h n)).edge
      (tracedRectifyRestrictionPath hX f h n).edge := by
  rw [tracedRectifyRestrictionPath_edge]
  exact (tracedRectificationComposite f h n (tracedRectificationStage hX f h n)).triangle

/-- 保持した実三角形による、元の比較区間の合成式。 -/
lemma tracedRectifyComparison_trace (n : ℕ) :
    SSet.HomotopyCategory.homMk (h n).edge ≫
        SSet.HomotopyCategory.homMk
          (tracedRectificationStepPath f n (tracedRectificationStage hX f h n)).edge =
      SSet.HomotopyCategory.homMk (tracedRectifyRestrictionPath hX f h n).edge :=
  SSet.HomotopyCategory.homMk_comp_homMk (tracedRectifyComparison_triangle hX f h n)

end SerrePositivity.KST.Spectra.KanSequence
