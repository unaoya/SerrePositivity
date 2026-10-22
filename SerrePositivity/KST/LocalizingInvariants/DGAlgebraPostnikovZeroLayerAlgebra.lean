module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovZeroLayerNaturality
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroMapOver

/-!
概要：元の零切断と未 shift の層を、実分裂平方零代数と元の射へまとめる。
方針：零切断上の実係数作用と層射の作用保存を mapOver へ渡す。
規約：underlying 二成分は元の射そのもの。使われ方：作用を保つ係数逆の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (B : Mon (Complex R)) [B.X.IsStrictlyLE 0] (n : ℤ)

def postnikovZeroLayerAlgebra : Mon (Complex R) :=
  SquareZero.algebra (postnikov R B 0) (postnikovLayerZeroBimodule R B n)

variable {B} {C : Mon (Complex R)} [C.X.IsStrictlyLE 0] (f : B ⟶ C)

def postnikovZeroLayerAlgebraMap :
    postnikovZeroLayerAlgebra R B n ⟶ postnikovZeroLayerAlgebra R C n :=
  SquareZero.mapOver (postnikovMap R f 0) (postnikovLayerZeroBimodule R B n)
    (postnikovLayerZeroBimodule R C n) (postnikovLayerZeroMap R f n)

lemma postnikovZeroLayerAlgebraMap_hom : (postnikovZeroLayerAlgebraMap R n f).hom =
    biprod.map (postnikovMap R f 0).hom (postnikovLayerMap R f n) := rfl

lemma postnikovZeroLayerAlgebraMap_projection : postnikovZeroLayerAlgebraMap R n f ≫
    SquareZero.projection (postnikov R C 0) (postnikovLayerZeroBimodule R C n) =
      SquareZero.projection (postnikov R B 0) (postnikovLayerZeroBimodule R B n) ≫
        postnikovMap R f 0 := SquareZero.mapOver_projection _ _ _ _

lemma postnikovZeroLayerAlgebraMap_zeroSection :
    SquareZero.zeroSection (postnikov R B 0) (postnikovLayerZeroBimodule R B n) ≫
      postnikovZeroLayerAlgebraMap R n f = postnikovMap R f 0 ≫
        SquareZero.zeroSection (postnikov R C 0) (postnikovLayerZeroBimodule R C n) :=
  SquareZero.zeroSection_mapOver _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
