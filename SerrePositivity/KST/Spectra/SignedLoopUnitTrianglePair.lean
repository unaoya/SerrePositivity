module

public import SerrePositivity.KST.Spectra.TrianglePairComparison
public import SerrePositivity.KST.Spectra.SignedLoopUnitStructureTriangles

/-!
概要：単位構造の実合成・逆三角形を、高次比較が保持する一つの組へ束ねる。
方針：保存済みの同じ二単体と共有面の厳密等式を使い、指定した射で同時に写す。
規約：単位の実構造区間を選び直さない。使われ方：元の構造区間の自然性正方形。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
variable (X : OmegaSpectrum.{u})

/-- 実際の単位構造の三角形が値を取る、元の構造射の写像空間。 -/
abbrev signedLoopUnitStructureMappingSpace (n : ℕ) : SSet.{u} :=
  (PointedObject.basedHom (PointedSimplicialSet.circle.{u} ⊗ (X.level n).space)
    ((KanSequence.signedLoopTail X.toKanSequence).level (n + 1)).space).right

/-- 単位構造区間に実際に使う、保存済みの合成・逆向き三角形の組。 -/
def signedLoopUnitStructureTrianglePair (n : ℕ) :
    SquareAdjustment.TrianglePair (signedLoopUnitStructureMappingSpace X n) where
  forward := signedLoopUnitStructureCompositeTriangle X n
  inverse := signedLoopUnitStructureInverseTriangle X n
  shared := signedLoopUnitStructureTriangles_shared X n

variable {E : SSet.{u}} (n : ℕ) (m : signedLoopUnitStructureMappingSpace X n ⟶ E)

/-- 元の同じ二単体を段比較・入力作用などの指定された一つの射で写した組。 -/
def mappedSignedLoopUnitStructureTrianglePair : SquareAdjustment.TrianglePair E :=
  (signedLoopUnitStructureTrianglePair X n).map m

/-- 第一辺は、元の交換符号の同じ評価区間の指定像。 -/
lemma mappedSignedLoopUnitStructureTrianglePair_two :
    stdSimplex.δ (2 : Fin 3) ≫ (mappedSignedLoopUnitStructureTrianglePair X n m).forward =
      (KanSequence.signedLoopStructureFirstInterval
        X.toKanSequence X.toKanSequence_omega n).path ≫ m := by
  change stdSimplex.δ (2 : Fin 3) ≫ (signedLoopUnitStructureCompositeTriangle X n ≫ m) = _
  rw [← Category.assoc, signedLoopUnitStructureCompositeTriangle_two]

/-- 第二辺も、同じ自然な二重反転の評価区間の指定像。 -/
lemma mappedSignedLoopUnitStructureTrianglePair_zero :
    stdSimplex.δ (0 : Fin 3) ≫ (mappedSignedLoopUnitStructureTrianglePair X n m).forward =
      (KanSequence.signedLoopStructureSecondInterval X.toKanSequence n).path ≫ m := by
  change stdSimplex.δ (0 : Fin 3) ≫ (signedLoopUnitStructureCompositeTriangle X n ≫ m) = _
  rw [← Category.assoc, signedLoopUnitStructureCompositeTriangle_zero]

/-- 比較が回収する逆辺は、単位に実際に使う元の構造区間全体の指定像。 -/
lemma mappedSignedLoopUnitStructureTrianglePair_inverse_zero :
    stdSimplex.δ (0 : Fin 3) ≫ (mappedSignedLoopUnitStructureTrianglePair X n m).inverse =
      (signedLoopUnitStructurePath X n).path ≫ m := by
  change stdSimplex.δ (0 : Fin 3) ≫ (signedLoopUnitStructureInverseTriangle X n ≫ m) = _
  rw [← Category.assoc, signedLoopUnitStructureInverseTriangle_zero]

end SerrePositivity.KST.Spectra.OmegaSpectrum
