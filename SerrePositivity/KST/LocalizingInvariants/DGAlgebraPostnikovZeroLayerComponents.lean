module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovZeroLayerProInverse
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroSeparatedHomBimodule

/-!
概要：零底と層の実平方零代数射から、実底射と作用を保つ係数射を取り出す。
方針：負の層次数と零底の分離、元の乗法保存からの混合作用回収を適用する。
規約：元の順方向射の両成分を回収。使われ方：実代数 pro 逆の双加群成分。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {B C : Mon (Complex R)}
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] (n : ℤ)
  (r : postnikovZeroLayerAlgebra R B n ⟶ postnikovZeroLayerAlgebra R C n)

def postnikovZeroLayerHomBase : postnikov R B 0 ⟶ postnikov R C 0 :=
  SquareZero.SeparatedHom.base (postnikovLayerZeroBimodule R B n)
    (postnikovLayerZeroBimodule R C n) r

def postnikovZeroLayerHomCoefficient : postnikovLayer R B n ⟶ postnikovLayer R C n :=
  SquareZero.SeparatedHom.coefficient (postnikovLayerZeroBimodule R B n)
    (postnikovLayerZeroBimodule R C n) r

local instance zeroLayerSourceBase_lowerBound : (postnikov R B 0).X.IsStrictlyGE 0 := by
  simpa only [neg_zero] using postnikov_lowerBound R B 0

local instance zeroLayerTargetBase_lowerBound : (postnikov R C 0).X.IsStrictlyGE 0 := by
  simpa only [neg_zero] using postnikov_lowerBound R C 0

local instance zeroLayerSource_upperBound :
    (postnikovLayerZeroBimodule R B n).X.IsStrictlyLE (-(n + 1)) :=
  postnikovLayer_upperBound R B n

local instance zeroLayerTarget_upperBound :
    (postnikovLayerZeroBimodule R C n).X.IsStrictlyLE (-(n + 1)) :=
  postnikovLayer_upperBound R C n

def postnikovZeroLayerHomBimoduleMap (hn : 0 ≤ n) : postnikovLayerZeroBimodule R B n ⟶
    bimoduleRestrict (postnikovZeroLayerHomBase R n r) (postnikovLayerZeroBimodule R C n) :=
  SquareZero.SeparatedHom.coefficientBimoduleMap (postnikovLayerZeroBimodule R B n)
    (postnikovLayerZeroBimodule R C n) r (-(n + 1)) (by omega)

lemma postnikovZeroLayerHomBimoduleMap_hom (hn : 0 ≤ n) :
    (postnikovZeroLayerHomBimoduleMap R n r hn).hom =
      postnikovZeroLayerHomCoefficient R n r := rfl

lemma postnikovZeroLayerHom_diagonal (hn : 0 ≤ n) : r.hom =
    biprod.map (postnikovZeroLayerHomBase R n r).hom
      (postnikovZeroLayerHomCoefficient R n r) :=
  SquareZero.SeparatedHom.hom_diagonal (postnikovLayerZeroBimodule R B n)
    (postnikovLayerZeroBimodule R C n) r (-(n + 1)) (by omega)

variable (f : B ⟶ C)

lemma postnikovZeroLayerHomBase_of_map :
    postnikovZeroLayerHomBase R n (postnikovZeroLayerAlgebraMap R n f) =
      postnikovMap R f 0 := by
  apply Mon.Hom.ext
  change (biprod.inl ≫ biprod.map (postnikovMap R f 0).hom
    (postnikovLayerMap R f n)) ≫ biprod.fst = (postnikovMap R f 0).hom
  rw [biprod.inl_map, Category.assoc, biprod.inl_fst, Category.comp_id]

lemma postnikovZeroLayerHomCoefficient_of_map :
    postnikovZeroLayerHomCoefficient R n (postnikovZeroLayerAlgebraMap R n f) =
      postnikovLayerMap R f n := by
  change biprod.inr ≫ biprod.map (postnikovMap R f 0).hom
    (postnikovLayerMap R f n) ≫ biprod.snd = postnikovLayerMap R f n
  rw [← Category.assoc, biprod.inr_map, Category.assoc, biprod.inr_snd, Category.comp_id]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
