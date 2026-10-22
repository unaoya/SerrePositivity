module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroConeMap
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovLayerBimoduleMap
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovPerturbedExtension

/-!
概要：元の dg 代数射から、Postnikov の微分変更代数の実代数射を構成する。
方針：元の層包含の自然性を、検証済みの追加微分の可換性へ渡す。
規約：底と層は元の比較射。使われ方：選択した cell class の自然性の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {B C : Mon (Complex R)}
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] (f : B ⟶ C) (n : ℤ) (hn : 0 ≤ n)

local instance perturbedMapLayerLower (D : Mon (Complex R)) [D.X.IsStrictlyLE 0] :
    (postnikovLayerBimodule R D n).X.IsStrictlyGE (-(n + 1)) :=
  postnikovLayer_lowerBound R D n

local instance perturbedMapLayerUpper (D : Mon (Complex R)) [D.X.IsStrictlyLE 0] :
    (postnikovLayerBimodule R D n).X.IsStrictlyLE (-(n + 1)) :=
  postnikovLayer_upperBound R D n

def postnikovPerturbedMap : postnikovPerturbedExtension R B n hn ⟶
    postnikovPerturbedExtension R C n hn :=
  SquareZeroCone.map (postnikovMap R f (n + 1)) (postnikovLayerBimodule R B n)
    (postnikovLayerBimodule R C n) (postnikovLayerBimoduleMap R f n)
    (postnikovLayerInclusionBimodule R B n) (postnikovLayerInclusionBimodule R C n)
    (postnikovLayerMap_inclusion R f n) (-(n + 1)) (by omega)

lemma postnikovPerturbedMap_f (p : ℤ) : (postnikovPerturbedMap R f n hn).hom.f p =
    (biprod.map (postnikovMap R f (n + 1)).hom ((postnikovLayerMap R f n)⟦(1 : ℤ)⟧')).f p :=
  SquareZeroCone.map_f _ _ _ _ _ _ _ _ _ p

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
