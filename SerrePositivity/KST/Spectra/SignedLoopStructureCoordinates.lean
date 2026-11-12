module

public import SerrePositivity.KST.Spectra.SignedLoopStructurePaths

/-!
概要：符号付き随伴比較の二端点を、元のスペクトル構造射の curry と厳密に同定する。
方針：元の随伴構造式と Kan 円への制限式を用いる。
規約：成分でなく射の等式。使われ方：保持した実三角形から単位構造区間への端点照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.KanSequence

/-- 元の構造像の curry は、保存した符号付き比較の同じ左端点。 -/
lemma signedAdjoint_structure_left (X : KanSequence.{u}) (n : ℕ) :
    curry (PointedSimplicialSet.circle.{u} ◁ kanAdjoint X n ≫ (signedLoopTail X).sigma n) =
      SignedAdjointPaths.left (kanAdjoint X n) (kanAdjoint X (n + 1)) := by
  erw [curry_natural_left]
  change kanAdjoint X n ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _ ((signedLoopTail X).sigma n) = _
  erw [signedLoopTail_adjoint X n, ← kanAdjoint_comparison X (n + 1)]
  rfl

/-- 元の次段構造制限の curry は、保存した符号付き比較の同じ右端点。 -/
lemma signedAdjoint_structure_right (X : KanSequence.{u}) (n : ℕ) :
    curry (X.sigma n ≫ kanAdjoint X (n + 1)) =
      SignedAdjointPaths.right (kanAdjoint X n) (kanAdjoint X (n + 1)) := by
  erw [curry_natural_right]
  change _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _ (X.sigma n) ≫
    (ihom PointedSimplicialSet.circle.{u}).map (kanAdjoint X (n + 1)) = _
  erw [← kanAdjoint_comparison X n]
  rfl

end SerrePositivity.KST.Spectra.KanSequence
