module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassTransitionWitness

/-!
概要：遷移した元の分子 class を、A の元の低い段の標準 class と実経路で比較する。
方針：既存の class 自然性経路を同じ cell 共通源へ移し、底の定数射影も回収する。
規約：同じ A の遷移と元の分子を保持。使われ方：次の切断の実逆の class 整合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} (hn : 0 ≤ n)
  {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (lowerFunctor R n hn)) i m hi)
  (d : PostnikovCommonLayerInverse R hn f c) {j : ℕ} (hj : j ≤ i)

attribute [local instance] PostnikovRoofZeroSpan.refined_source_nonpositive
  PostnikovRoofZeroSpan.refined_target_nonpositive

def postnikovCommonClassStandard : cellResolution R (postnikovCommonClassBase R hn f c d) ⟶
    SquareZero.algebra (postnikovCommonClassBase R hn f c d)
      (postnikovCommonClassTransitionLayer R hn f c d hj) :=
  postnikovCellClassOver R (A.obj j).obj (postnikovCommonClassBase R hn f c d) n hn
    (postnikovCommonClassRetractBase R hn f c d (hj := hj))

def postnikovCommonClassStandardEndpoint :=
  postnikovCommonRightGlueToCell R hn f c d ≫ postnikovCommonClassStandard R hn f c d hj

/-- 源は既存の右像貼合せと同じ非正次数代数。 -/
def postnikovCommonClassStandardWitness : Path.Witness R
    (postnikovCommonClassTransitionTarget R hn f c d (hj := hj))
    (postnikovCommonClassStandardEndpoint R hn f c d hj) := by
  let w := ((postnikovCellClassOverImageWitness R (A.obj i).obj (A.obj j).obj
    (postnikovCommonClassBase R hn f c d) n hn
    (roofRefine R hn f c d.zero.source_le).roof.numerator
    (A.transition hj).hom).precompNonpositiveCell R).precomp
      (cellPathNonpositiveProjection R (postnikovCommonRightCellSource R hn f c d))
  refine ⟨w.hom, ?_, ?_⟩
  · simpa only [postnikovCommonClassTransitionTarget, postnikovCommonRightGlueToCell,
      postnikovCommonClassTarget, postnikovCommonClassTransitionMap,
      postnikovCommonClassTransitionCoefficient, postnikovCommonClassTransitionLayer,
      postnikovCommonClassRetractBase, postnikovCommonClassBase, Category.assoc] using w.source_eq
  · simpa only [postnikovCommonClassStandardEndpoint, postnikovCommonRightGlueToCell,
      postnikovCommonClassStandard, postnikovCommonClassTransitionLayer,
      postnikovCommonClassRetractBase, postnikovCommonClassBase, Category.assoc] using w.target_eq

lemma postnikovCommonClassStandardEndpoint_projection :
    postnikovCommonClassStandardEndpoint R hn f c d hj ≫ SquareZero.projection _ _ =
      postnikovCommonRightZeroGlueProjection R hn f c d := by
  rw [postnikovCommonClassStandardEndpoint, Category.assoc, postnikovCommonClassStandard,
    postnikovCellClassOver_projection, postnikovCommonRightGlueToCell_projection]

lemma postnikovCommonClassStandardWitness_projection :
    (postnikovCommonClassStandardWitness R hn f c d hj).hom ≫ Path.map R (SquareZero.projection _ _) =
      postnikovCommonRightZeroGlueProjection R hn f c d ≫
        Path.diagonal R (postnikovCommonClassBase R hn f c d) := by
  let P := postnikovCommonClassBase R hn f c d
  let ε := cellPathNonpositiveProjection R (postnikovCommonRightCellSource R hn f c d)
  let κ := cellPathNonpositiveToDoubleCell R P
  let w₀ := postnikovCellClassOverImageWitness R (A.obj i).obj (A.obj j).obj P n hn
    (roofRefine R hn f c d.zero.source_le).roof.numerator (A.transition hj).hom
  change (ε ≫ (κ ≫ w₀.hom)) ≫ Path.map R (SquareZero.projection _ _) = _
  rw [Category.assoc, Category.assoc, postnikovCellClassOverImageWitness_relative]
  simp only [Category.assoc]
  rw [← Category.assoc κ, cellPathNonpositiveToDoubleCell_toCell]
  rw [← Category.assoc, ← Category.assoc]
  change (postnikovCommonRightGlueToCell R hn f c d ≫ cellAugmentation R P) ≫
    Path.diagonal R P = _
  rw [postnikovCommonRightGlueToCell_projection]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
