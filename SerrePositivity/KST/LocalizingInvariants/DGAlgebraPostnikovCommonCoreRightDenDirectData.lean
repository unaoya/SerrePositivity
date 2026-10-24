module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellFactorizationDirectImage
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightDenCompositeZero

/-!
概要：元の分母段から j への直接 B 遷移と、その二段因子分解の係数表示を固定する。
方針：塔の厳密な合成式と、元の係数表示の同型を使う。
規約：元の B 遷移そのものを保持。使われ方：分母の直接自然性と二段合成の実比較。
-/

@[expose] public section
noncomputable section
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

def postnikovCommonRightDenDirectMap : (B.obj d.zero.stage).obj ⟶ (B.obj j).obj :=
  (B.transition (hj.trans (d.zero.inverse_le.trans d.zero.stage_le))).hom

lemma postnikovCommonRightDenDirect_factorization :
    (B.transition (d.zero.inverse_le.trans d.zero.stage_le)).hom ≫ (B.transition hj).hom =
      postnikovCommonRightDenDirectMap R hn f c d hj :=
  congrArg (fun k => k.hom) (B.transition_comp (d.zero.inverse_le.trans d.zero.stage_le) hj)

def postnikovCommonRightDenDirectImageIso :=
  postnikovCellFactorizationImageIso R (B.obj d.zero.stage).obj (B.obj j).obj
    (postnikovCommonClassBase R hn f c d) n hn
    (roofRefine R hn f c d.zero.source_le).roof.denominator
    (postnikovCommonRightDenDirectMap R hn f c d hj) (B.obj i).obj
    (B.transition (d.zero.inverse_le.trans d.zero.stage_le)).hom (B.transition hj).hom
    (postnikovCommonRightDenDirect_factorization R hn f c d hj)

def postnikovCommonRightDenDirectToZero :=
  (postnikovCommonRightDenDirectImageIso R hn f c d hj).hom ≫
    (postnikovCommonRightDenCompositeZeroIso R hn f c d hj).hom

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
