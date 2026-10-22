module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellImageForward
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovClassZeroNaturality

/-!
概要：第一 ImageWitness を第二係数射で写して零底へ戻した全経路を計算する。
方針：底変更の可換式と class の零底自然性を、元の全経路の後合成へ代入する。
規約：指定した第一自然性経路を保持。使われ方：元の T の B 遷移後の像の同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (B C D P : Mon (Complex R))
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] [D.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n) (b : P ⟶ postnikov R B n) (f : B ⟶ C) (g : C ⟶ D)

lemma postnikovCellImageForwardRelative_zero_map :
    (postnikovCellImageForwardRelative R B C D P n hn b f g).hom ≫ Path.map R
      (SquareZero.baseChangeMap ((b ≫ postnikovMap R f n) ≫ postnikovMap R g n)
        (postnikovShiftedLayerBimodule R D n hn 1) ≫ postnikovClassToZeroBase R D n hn 1) =
    (postnikovCellImageRelative R B C P n hn b f).hom ≫ Path.map R
      (SquareZero.baseChangeMap (b ≫ postnikovMap R f n)
        (postnikovShiftedLayerBimodule R C n hn 1) ≫ postnikovClassToZeroBase R C n hn 1) ≫
          Path.map R (postnikovZeroClassMap R n 1 g) := by
  change ((postnikovCellImageRelative R B C P n hn b f).hom ≫
    Path.map R (postnikovCellImageForwardMap R B C D P n hn b f g)) ≫ _ = _
  simp only [Category.assoc, ← Path.map_comp,
    reassoc_of% (postnikovCellImageForwardMap_map R B C D P n hn b f g),
    postnikovClassToZeroBase_naturality]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
