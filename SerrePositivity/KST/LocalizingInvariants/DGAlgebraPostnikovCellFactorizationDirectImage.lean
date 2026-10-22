module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellFactorizationDirectCommon

/-!
概要：P 上へ戻した直接経路を、元の単一 ImageWitness の全経路そのものへ同定する。
方針：P 射影と元の class 自然性への射影を比較し、経路 pullback の一意性を使う。
規約：同じ四重 cell 源を保持。使われ方：分母の直接遷移と二段合成の実比較。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (B D P : Mon (Complex R))
  [B.X.IsStrictlyLE 0] [D.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n) (b : P ⟶ postnikov R B n) (h : B ⟶ D)
  (C : Mon (Complex R)) [C.X.IsStrictlyLE 0]
  (f : B ⟶ C) (g : C ⟶ D) (heq : f ≫ g = h)

lemma postnikovCellFactorizationDirectCommon_image_hom :
    (postnikovCellFactorizationDirectCommonWitness R B D P n hn b h C f g heq).hom =
    postnikovCellImageToSecond R P ≫
      (postnikovCellImageRelative R B D P n hn b h).hom := by
  apply SquareZero.baseChangePath_hom_ext (b ≫ postnikovMap R h n)
    (postnikovShiftedLayerBimodule R D n hn 1)
  · calc
      _ = postnikovCellFactorizationProjection R P ≫ Path.diagonal R P :=
        (postnikovCellFactorizationDirectCommonWitness R B D P n hn b h C f g heq).projection_eq
      _ = _ := by
        rw [Category.assoc, (postnikovCellImageRelative R B D P n hn b h).projection_eq,
          ← Category.assoc, postnikovCellImageToSecond_projection]
  · let hl := SquareZero.baseChangeRelativeWitness_map (b ≫ postnikovMap R h n)
      (postnikovShiftedLayerBimodule R D n hn 1) (postnikovCellFactorizationProjection R P)
      (postnikovCellFactorizationDirectWitness R B D P n hn b h C f g heq)
    let hr := congrArg (fun k => postnikovCellImageToSecond R P ≫ k)
      (postnikovCellImageRelative_map R B D P n hn b h)
    exact ((hl.trans (postnikovCellFactorizationDirectClass_hom R B D P n hn b h C f g heq)).trans
      hr.symm).trans (Category.assoc _ _ _).symm

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
