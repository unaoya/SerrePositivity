module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSourceImageFactorSquare

/-!
概要：源側像拡大を非正次数 dg 代数の矢印圏上の実関手にし、元の源比較を自然変換にする。
方針：元の正方形射の恒等・合成則と source factor の厳密な自然性を包装する。
規約：値は実 dg 代数、射は構成済みの実射。使われ方：LT の連結なレベル表示の図式。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (n : ℤ) (hn : 0 ≤ n)

lemma postnikovSourceImageArrow_condition {f g : Arrow (NonpositiveAlgebra R)} (a : f ⟶ g) :
    f.hom.hom ≫ a.right.hom = a.left.hom ≫ g.hom.hom :=
  (congrArg (fun z : f.left ⟶ g.right => z.hom) a.w).symm

def postnikovSourceImageArrowFunctor : Arrow (NonpositiveAlgebra R) ⥤ Mon (Complex R) where
  obj f := postnikovSourceImageExtension R f.hom.hom n hn
  map a := postnikovSourceImageExtensionSquareMap R n hn _ _ a.left.hom a.right.hom
    (postnikovSourceImageArrow_condition R a)
  map_id f := postnikovSourceImageExtensionSquareMap_id R n hn f.hom.hom
  map_comp a b := postnikovSourceImageExtensionSquareMap_comp R n hn _ _ _
    a.left.hom a.right.hom b.left.hom b.right.hom
    (postnikovSourceImageArrow_condition R a) (postnikovSourceImageArrow_condition R b)

def postnikovSourceImageArrowSource :
    (Arrow.leftFunc : Arrow (NonpositiveAlgebra R) ⥤ NonpositiveAlgebra R) ⋙
      postnikovFunctor R (n + 1) ⟶ postnikovSourceImageArrowFunctor R n hn where
  app f := postnikovSourceImageFactor R f.hom.hom n hn
  naturality {_ _} a := postnikovSourceImageFactor_square R n hn _ _ a.left.hom a.right.hom
    (postnikovSourceImageArrow_condition R a)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
