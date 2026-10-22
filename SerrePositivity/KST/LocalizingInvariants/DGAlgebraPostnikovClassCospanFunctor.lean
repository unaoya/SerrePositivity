module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSourceImageArrowFunctor
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackFunctor

/-!
概要：元の Postnikov class と零切断の実 cospan を、非正次数代数上の厳密な関手にする。
方針：元の三成分と class の厳密な自然性を cospan の自然変換へ渡す。
規約：選択した cell lift を使用しない。使われ方：標的 class 模型の関手化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {B C D : Mon (Complex R)}
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] [D.X.IsStrictlyLE 0] (n : ℤ) (hn : 0 ≤ n)

lemma postnikovDerivationTargetMap_id : postnikovDerivationTargetMap R (𝟙 B) n hn = 𝟙 _ := by
  apply Mon.Hom.ext
  rw [postnikovDerivationTargetMap_hom, postnikovLayerMap_id]
  have hb : (postnikovMap R (𝟙 B) n).hom = 𝟙 _ := (postnikovComplex R n).map_id B
  have hs := (CategoryTheory.shiftFunctor (Complex R) (1 : ℤ)).map_id (postnikovLayer R B n)
  rw [hb, hs]
  exact cochainBiprodMap_id

lemma postnikovDerivationTargetMap_comp (f : B ⟶ C) (g : C ⟶ D) :
    postnikovDerivationTargetMap R (f ≫ g) n hn =
      postnikovDerivationTargetMap R f n hn ≫ postnikovDerivationTargetMap R g n hn := by
  apply Mon.Hom.ext
  change (postnikovDerivationTargetMap R (f ≫ g) n hn).hom =
    (postnikovDerivationTargetMap R f n hn).hom ≫ (postnikovDerivationTargetMap R g n hn).hom
  rw [postnikovDerivationTargetMap_hom, postnikovDerivationTargetMap_hom,
    postnikovDerivationTargetMap_hom, cochainBiprodMap_comp, postnikovLayerMap_comp]
  have hb : (postnikovMap R (f ≫ g) n).hom =
      (postnikovMap R f n).hom ≫ (postnikovMap R g n).hom := (postnikovComplex R n).map_comp f g
  rw [hb, (CategoryTheory.shiftFunctor (Complex R) (1 : ℤ)).map_comp]

def postnikovClassCospanFunctor : NonpositiveAlgebra R ⥤ (WalkingCospan ⥤ Mon (Complex R)) where
  obj B := cospan (postnikovPerturbedClass R B.obj n hn)
    (SquareZero.zeroSection (postnikov R B.obj n) (postnikovShiftedLayerBimodule R B.obj n hn 1))
  map f := cospanHomMk (postnikovDerivationTargetMap R f.hom n hn)
    (postnikovPerturbedMap R f.hom n hn) (postnikovMap R f.hom n)
    (postnikovPerturbedClass_naturality R f.hom n hn).symm
    (postnikovDerivationTargetMap_zeroSection R f.hom n hn)
  map_id B := by
    apply NatTrans.ext
    funext j
    rcases j with _ | (_ | _)
    · exact postnikovDerivationTargetMap_id R n hn
    · exact postnikovPerturbedMap_id R n hn
    · exact postnikovMap_identity R n
  map_comp f g := by
    apply NatTrans.ext
    funext j
    rcases j with _ | (_ | _)
    · exact postnikovDerivationTargetMap_comp R n hn f.hom g.hom
    · exact postnikovPerturbedMap_comp R n hn f.hom g.hom
    · exact postnikovMap_composition R n f.hom g.hom

def postnikovClassModelFunctor : NonpositiveAlgebra R ⥤ Mon (Complex R) :=
  postnikovClassCospanFunctor R n hn ⋙ HomotopyPullbackModel.diagramFunctor R

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
