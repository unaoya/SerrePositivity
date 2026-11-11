module

public import SerrePositivity.KST.Spectra.SignedLoopTracedStructureInterval

/-!
概要：保持した構造合成三角形の三面を、元の交換符号・二重反転・合成の実辺へ同定する。
方針：同じ二単体の面を元の評価射へ写す。
規約：二辺と充填を再選択しない。使われ方：単位構造区間の高次比較の指定三角形。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.KanSequence
variable (X : KanSequence.{u}) (hX : X.OmegaCondition)

/-- 元の交換符号の実辺を、同じ評価で uncurry した構造区間。 -/
def signedLoopStructureFirstInterval (n : ℕ) :=
  (SignedAdjointPaths.firstPath
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _ (X.sigma (n + 2))) (hX (n + 2))
    (kanAdjoint X n) (kanAdjoint X (n + 1))).basedUncurry

/-- 同じ自然な二重反転の実辺を、元の評価で uncurry した構造区間。 -/
def signedLoopStructureSecondInterval (n : ℕ) :=
  (SignedAdjointPaths.secondPath (kanAdjoint X n) (kanAdjoint X (n + 1))).basedUncurry

/-- 合成三角形の第一辺は、元の交換符号区間の同じ評価像。 -/
lemma signedLoopStructureCompositeTriangle_two (n : ℕ) :
    stdSimplex.δ (2 : Fin 3) ≫ signedLoopStructureCompositeTriangle X hX n =
      (signedLoopStructureFirstInterval X hX n).path := by
  rw [signedLoopStructureCompositeTriangle, signedLoopStructureComposite, ← Category.assoc,
    SignedAdjointPaths.forwardComposite_two]
  exact (SignedAdjointPaths.firstPath
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _ (X.sigma (n + 2))) (hX (n + 2))
    (kanAdjoint X n) (kanAdjoint X (n + 1))).basedUncurry_path.symm

/-- 合成三角形の第二辺は、同じ自然な二重反転区間の評価像。 -/
lemma signedLoopStructureCompositeTriangle_zero (n : ℕ) :
    stdSimplex.δ (0 : Fin 3) ≫ signedLoopStructureCompositeTriangle X hX n =
      (signedLoopStructureSecondInterval X n).path := by
  rw [signedLoopStructureCompositeTriangle, signedLoopStructureComposite, ← Category.assoc,
    SignedAdjointPaths.forwardComposite_zero]
  exact (SignedAdjointPaths.secondPath
    (kanAdjoint X n) (kanAdjoint X (n + 1))).basedUncurry_path.symm

/-- 合成三角形の対角辺も、同じ充填で得た合成区間全体の評価像。 -/
lemma signedLoopStructureCompositeTriangle_one (n : ℕ) :
    stdSimplex.δ (1 : Fin 3) ≫ signedLoopStructureCompositeTriangle X hX n =
      (signedLoopStructureComposite X hX n).path.basedUncurry.path := by
  rw [signedLoopStructureCompositeTriangle, signedLoopStructureComposite, ← Category.assoc,
    SignedAdjointPaths.forwardComposite_one]
  exact (signedLoopStructureComposite X hX n).path.basedUncurry_path.symm

end SerrePositivity.KST.Spectra.KanSequence
