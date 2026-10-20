module

public import SerrePositivity.KST.Spectra.SignedLoopUnitTrianglePair

/-!
概要：単位構造の三辺の実正方形から、元の構造区間の指定像同士の比較を回収する。
方針：保存済み合成・逆三角形を同じ射で写し、非定値な共有境界を保って二段で比較する。
規約：入力三正方形の存在は別途証明する。使われ方：全 Hom の主構造正方形の構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
open SquareAdjustment
variable (X Y : OmegaSpectrum.{u}) (n k : ℕ) {E : SSet.{u}} [KanComplex E]
  (m₀ : signedLoopUnitStructureMappingSpace X n ⟶ E)
  (m₁ : signedLoopUnitStructureMappingSpace Y k ⟶ E)

variable
  (H : SSet.Homotopy
    (stdSimplex.δ (2 : Fin 3) ≫ (mappedSignedLoopUnitStructureTrianglePair X n m₀).forward)
    (stdSimplex.δ (2 : Fin 3) ≫ (mappedSignedLoopUnitStructureTrianglePair Y k m₁).forward))
  (V : SSet.Homotopy
    (stdSimplex.δ (0 : Fin 3) ≫ (mappedSignedLoopUnitStructureTrianglePair X n m₀).forward)
    (stdSimplex.δ (0 : Fin 3) ≫ (mappedSignedLoopUnitStructureTrianglePair Y k m₁).forward))
  (U : SSet.Homotopy
    (stdSimplex.δ (1 : Fin 3) ≫ (mappedSignedLoopUnitStructureTrianglePair X n m₀).inverse)
    (stdSimplex.δ (1 : Fin 3) ≫ (mappedSignedLoopUnitStructureTrianglePair Y k m₁).inverse))
  (hm : rightSide ≫ H.h = leftSide ≫ V.h)
  (hl : leftSide ≫ H.h = leftSide ≫ U.h)

/-- 実単位構造の同じ四つの三角形と三つの入力正方形を保持する二段の相対比較。 -/
def signedLoopUnitStructureTriangleComparison :
    TrianglePairComparison (mappedSignedLoopUnitStructureTrianglePair X n m₀)
      (mappedSignedLoopUnitStructureTrianglePair Y k m₁) H V U hm hl :=
  TrianglePairComparison.choose (mappedSignedLoopUnitStructureTrianglePair X n m₀)
    (mappedSignedLoopUnitStructureTrianglePair Y k m₁) H V U hm hl

/-- 回収する二辺は、単位に実際に使う元の構造区間全体の指定像そのもの。 -/
def signedLoopUnitStructureComparisonSquare :
    SSet.Homotopy ((signedLoopUnitStructurePath X n).path ≫ m₀)
      ((signedLoopUnitStructurePath Y k).path ≫ m₁) := by
  let C := signedLoopUnitStructureTriangleComparison X Y n k m₀ m₁ H V U hm hl
  let S := TrianglePairComparison.square
    (mappedSignedLoopUnitStructureTrianglePair X n m₀)
    (mappedSignedLoopUnitStructureTrianglePair Y k m₁) H V U hm hl C
  exact {
    h := S.h
    h₀ := S.h₀.trans (mappedSignedLoopUnitStructureTrianglePair_inverse_zero X n m₀)
    h₁ := S.h₁.trans (mappedSignedLoopUnitStructureTrianglePair_inverse_zero Y k m₁)
    rel := by ext j ⟨⟨s, hs⟩, t⟩; exact hs.elim }

/-- 左境界全体は元の二重反転辺の正方形の終境界を保持する。 -/
lemma signedLoopUnitStructureComparisonSquare_left :
    leftSide ≫ (signedLoopUnitStructureComparisonSquare X Y n k m₀ m₁ H V U hm hl).h =
      rightSide ≫ V.h :=
  TrianglePairComparison.left (mappedSignedLoopUnitStructureTrianglePair X n m₀)
    (mappedSignedLoopUnitStructureTrianglePair Y k m₁) H V U hm hl
    (signedLoopUnitStructureTriangleComparison X Y n k m₀ m₁ H V U hm hl)

/-- 右境界全体は元の定数辺の正方形の終境界を保持する。 -/
lemma signedLoopUnitStructureComparisonSquare_right :
    rightSide ≫ (signedLoopUnitStructureComparisonSquare X Y n k m₀ m₁ H V U hm hl).h =
      rightSide ≫ U.h :=
  TrianglePairComparison.right (mappedSignedLoopUnitStructureTrianglePair X n m₀)
    (mappedSignedLoopUnitStructureTrianglePair Y k m₁) H V U hm hl
    (signedLoopUnitStructureTriangleComparison X Y n k m₀ m₁ H V U hm hl)

end SerrePositivity.KST.Spectra.OmegaSpectrum
