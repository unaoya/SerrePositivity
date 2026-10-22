module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassTransitionWitness

/-!
概要：遷移した元の分子 class を、A の元の低い段の標準 class と実経路で比較する。
方針：既存の class 自然性経路を同じ cell 共通源へ移し、底の定数射影も回収する。
規約：同じ A の遷移と元の分子を保持。使われ方：二切断の実逆の class 整合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  (d : PostnikovCommonLayerInverse R f c) {j : ℕ} (hj : j ≤ i)

def postnikovCommonClassStandard : cellResolution R (postnikovCommonClassBase R f c d) ⟶
    SquareZero.algebra (postnikovCommonClassBase R f c d)
      (postnikovCommonClassTransitionLayer R f c d hj) :=
  postnikovCellClassOver R (A.obj j).obj (postnikovCommonClassBase R f c d) 1 (by omega)
    (postnikovCommonClassRetractBase R f c d (hj := hj))

def postnikovCommonClassStandardEndpoint :=
  postnikovCommonRightGlueToCell R f c d ≫ postnikovCommonClassStandard R f c d hj

/-- 源は既存の右像貼合せと同じ非正次数代数。 -/
def postnikovCommonClassStandardWitness : Path.Witness R
    (postnikovCommonClassTransitionTarget R f c d (hj := hj))
    (postnikovCommonClassStandardEndpoint R f c d hj) := by
  let w := ((postnikovCellClassOverImageWitness R (A.obj i).obj (A.obj j).obj
    (postnikovCommonClassBase R f c d) 1 (by omega)
    (postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator
    (A.transition hj).hom).precompNonpositiveCell R).precomp
      (cellPathNonpositiveProjection R (postnikovCommonRightCellSource R f c d))
  refine ⟨w.hom, ?_, ?_⟩
  · simpa only [postnikovCommonClassTransitionTarget, postnikovCommonRightGlueToCell,
      postnikovCommonClassTarget, postnikovCommonClassTransitionMap,
      postnikovCommonClassTransitionCoefficient, postnikovCommonClassTransitionLayer,
      postnikovCommonClassRetractBase, postnikovCommonClassBase, Category.assoc] using w.source_eq
  · simpa only [postnikovCommonClassStandardEndpoint, postnikovCommonRightGlueToCell,
      postnikovCommonClassStandard, postnikovCommonClassTransitionLayer,
      postnikovCommonClassRetractBase, postnikovCommonClassBase, Category.assoc] using w.target_eq

lemma postnikovCommonClassStandardEndpoint_projection :
    postnikovCommonClassStandardEndpoint R f c d hj ≫ SquareZero.projection _ _ =
      postnikovCommonRightZeroGlueProjection R f c d := by
  rw [postnikovCommonClassStandardEndpoint, Category.assoc, postnikovCommonClassStandard,
    postnikovCellClassOver_projection, postnikovCommonRightGlueToCell_projection]

lemma postnikovCommonClassStandardWitness_projection :
    (postnikovCommonClassStandardWitness R f c d hj).hom ≫ Path.map R (SquareZero.projection _ _) =
      postnikovCommonRightZeroGlueProjection R f c d ≫
        Path.diagonal R (postnikovCommonClassBase R f c d) := by
  let P := postnikovCommonClassBase R f c d
  let ε := cellPathNonpositiveProjection R (postnikovCommonRightCellSource R f c d)
  let κ := cellPathNonpositiveToDoubleCell R P
  let w₀ := postnikovCellClassOverImageWitness R (A.obj i).obj (A.obj j).obj P 1 (by omega)
    (postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator (A.transition hj).hom
  change (ε ≫ (κ ≫ w₀.hom)) ≫ Path.map R (SquareZero.projection _ _) = _
  rw [Category.assoc, Category.assoc, postnikovCellClassOverImageWitness_relative]
  simp only [Category.assoc]
  rw [← Category.assoc κ, cellPathNonpositiveToDoubleCell_toCell]
  rw [← Category.assoc, ← Category.assoc]
  change (postnikovCommonRightGlueToCell R f c d ≫ cellAugmentation R P) ≫
    Path.diagonal R P = _
  rw [postnikovCommonRightGlueToCell_projection]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
