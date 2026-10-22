module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellFactorizationImageIso
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellImageCompositeMap

/-!
概要：既存の因子分解 affine 経路を、元の二 ImageWitness の affine 合成そのものへ同定する。
方針：同じ四重源で両経路の P 射影と全 class 射影を照合し、経路 pullback の一意性を使う。
規約：class 経路の一致は結論。使われ方：元の Γ の右貼合せ境界との実照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R]

def postnikovCellImageToSecond (P : Mon (Complex R)) :
    cellResolution R (cellResolution R (cellResolution R (cellResolution R P))) ⟶
      cellResolution R (cellResolution R P) :=
  cellAugmentation R (cellResolution R (cellResolution R (cellResolution R P))) ≫
    cellAugmentation R (cellResolution R (cellResolution R P))

lemma postnikovCellImageToSecond_projection (P : Mon (Complex R)) :
    postnikovCellImageToSecond R P ≫
      (cellAugmentation R (cellResolution R P) ≫ cellAugmentation R P) =
      postnikovCellFactorizationProjection R P := by
  simp only [postnikovCellImageToSecond, postnikovCellFactorizationProjection, Category.assoc]

variable (B D P : Mon (Complex R)) [B.X.IsStrictlyLE 0] [D.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n) (b : P ⟶ postnikov R B n) (h : B ⟶ D)
  (C : Mon (Complex R)) [C.X.IsStrictlyLE 0]
  (f : B ⟶ C) (g : C ⟶ D) (heq : f ≫ g = h)

/-- 同じ四重 cell 源上で、元の二自然性経路の affine 合成に厳密に一致する。 -/
lemma postnikovCellFactorizationImagePath_hom :
    (postnikovCellFactorizationAffineCommonWitness R B D P n hn b h C f g heq).hom ≫
      Path.map R (postnikovCellFactorizationImageIso R B D P n hn b h C f g heq).hom =
    postnikovCellImageToSecond R P ≫ (postnikovCellImageComposite R B C D P n hn b f g).hom := by
  apply SquareZero.baseChangePath_hom_ext
    ((b ≫ postnikovMap R f n) ≫ postnikovMap R g n)
    (postnikovShiftedLayerBimodule R D n hn 1)
  · calc
      _ = postnikovCellFactorizationProjection R P ≫ Path.diagonal R P := by
        rw [Category.assoc, ← Path.map_comp, postnikovCellFactorizationImageIso_projection,
          (postnikovCellFactorizationAffineCommonWitness R B D P n hn b h C f g heq).projection_eq]
      _ = _ := by
        rw [Category.assoc, (postnikovCellImageComposite R B C D P n hn b f g).projection_eq,
          ← Category.assoc, postnikovCellImageToSecond_projection]
  · refine (postnikovCellFactorizationImageClass_map R B D P n hn b h C f g heq).trans ?_
    have hm := congrArg (fun t => postnikovCellImageToSecond R P ≫ t)
      (postnikovCellImageComposite_map R B C D P n hn b f g)
    change cellAugmentation R (cellResolution R (cellResolution R (cellResolution R P))) ≫
      (cellAugmentation R (cellResolution R (cellResolution R P)) ≫ _) = _
    exact (Category.assoc _ _ _).symm.trans
      (hm.symm.trans (Category.assoc _ _ _).symm)

lemma postnikovCellFactorizationImagePath_inv_hom :
    (postnikovCellFactorizationAffineCommonWitness R B D P n hn b h C f g heq).hom =
    (postnikovCellImageToSecond R P ≫ (postnikovCellImageComposite R B C D P n hn b f g).hom) ≫
      Path.map R (postnikovCellFactorizationImageIso R B D P n hn b h C f g heq).inv :=
  (Iso.eq_comp_inv ((Path.functor R).mapIso
    (postnikovCellFactorizationImageIso R B D P n hn b h C f g heq))).mpr
      (postnikovCellFactorizationImagePath_hom R B D P n hn b h C f g heq)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
