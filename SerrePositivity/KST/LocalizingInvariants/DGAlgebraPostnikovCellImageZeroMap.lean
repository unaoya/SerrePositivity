module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellImageRelative
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovClassBaseZeroIso

/-!
概要：元の ImageWitness の全経路を、零 class 標的へ戻した像として計算する。
方針：底変更の全射影と零底への元の射を経路関手で合成する。
規約：選んだ自然性経路を保持。使われ方：輪郭の L と第二自然性経路の同定。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (B C P : Mon (Complex R))
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n) (b : P ⟶ postnikov R B n) (f : B ⟶ C)

lemma postnikovCellImageRelative_zero_map :
    (postnikovCellImageRelative R B C P n hn b f).hom ≫ Path.map R
      (SquareZero.baseChangeMap (b ≫ postnikovMap R f n)
        (postnikovShiftedLayerBimodule R C n hn 1) ≫ postnikovClassToZeroBase R C n hn 1) =
    (postnikovCellClassOverNaturalityWitness R B C P n hn b f).hom ≫
      Path.map R (postnikovClassToZeroBase R C n hn 1) := by
  rw [Path.map_comp, ← Category.assoc, postnikovCellImageRelative_map]
  rfl

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
