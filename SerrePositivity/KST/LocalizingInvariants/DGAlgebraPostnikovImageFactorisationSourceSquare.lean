module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovImageFactorisationSquare

/-!
概要：元の上段から元の標的までの実因子分解の源射は、元の正方形に厳密に自然である。
方針：元の二脚と定数経路を照合し、源側像拡大の source・toTarget の自然性を合成する。
規約：元の source 射を保持。使われ方：実関手間の元の二射の自然変換。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {B C B' C' : Mon (Complex R)}
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] [B'.X.IsStrictlyLE 0] [C'.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n)
  (f : B ⟶ C) (f' : B' ⟶ C') (s : B ⟶ B') (t : C ⟶ C') (h : f ≫ t = s ≫ f')

lemma postnikovImageFactorisationSource_square : postnikovMap R s (n + 1) ≫
    postnikovImageFactorisationSource R f' n hn = postnikovImageFactorisationSource R f n hn ≫
      postnikovImageFactorisationSquareMap R n hn f f' s t h := by
  apply HomotopyPullbackModel.hom_ext R (postnikovSourceImageToTarget R f' n hn)
    (postnikovHomotopyPullbackComparison R C' n hn)
  · rw [Category.assoc, postnikovImageFactorisationSource_comparison, Category.assoc,
      postnikovImageFactorisationSquareMap_comparison,
      ← Category.assoc (postnikovImageFactorisationSource R f n hn),
      postnikovImageFactorisationSource_comparison]
    exact postnikovSourceImageFactor_square R n hn f f' s t h
  · rw [Category.assoc, postnikovImageFactorisation_fac, Category.assoc,
      postnikovImageFactorisationSquareMap_target,
      ← Category.assoc (postnikovImageFactorisationSource R f n hn),
      postnikovImageFactorisation_fac]
    exact (postnikovMap_square R (n + 1) f f' s t h).symm
  · rw [Category.assoc, postnikovImageFactorisationSource_path, Category.assoc,
      postnikovImageFactorisationSquareMap_path,
      ← Category.assoc (postnikovImageFactorisationSource R f n hn),
      postnikovImageFactorisationSource_path]
    have hc : postnikovMap R s (n + 1) ≫
        (postnikovSourceImageFactor R f' n hn ≫ postnikovSourceImageToTarget R f' n hn) =
      (postnikovSourceImageFactor R f n hn ≫ postnikovSourceImageToTarget R f n hn) ≫
        postnikovClassModelMap R n hn t := by
      rw [← Category.assoc, postnikovSourceImageFactor_square R n hn f f' s t h, Category.assoc,
        ← postnikovSourceImageToTarget_square R n hn f f' s t h, ← Category.assoc]
    simpa only [Category.assoc, Path.diagonal_naturality] using congrArg
      (fun z => z ≫ Path.diagonal R (postnikovClassModel R C' n hn)) hc

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
