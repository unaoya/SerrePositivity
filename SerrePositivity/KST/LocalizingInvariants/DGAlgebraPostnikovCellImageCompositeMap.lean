module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellImageComposite

/-!
概要：元の二 ImageWitness の affine 合成を、指定した摂動二経路の class 合成に全射で同定する。
方針：実 affine 線形式に第一辺・中点・第二辺の厳密な底変更式を代入する。
規約：任意の class 経路の一致は仮定しない。使われ方：Γ の貼合せ経路の具体的照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Preadditive
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (B C D P : Mon (Complex R))
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] [D.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n) (b : P ⟶ postnikov R B n) (f : B ⟶ C) (g : C ⟶ D)

lemma postnikovCellImageComposition_middle_constant_map :
    ((cellAugmentation R (cellResolution R P) ≫
      postnikovCellClassOver R C P n hn (b ≫ postnikovMap R f n) ≫
        postnikovCellImageForwardMap R B C D P n hn b f g) ≫ Path.diagonal R _) ≫
      Path.map R (SquareZero.baseChangeMap
        ((b ≫ postnikovMap R f n) ≫ postnikovMap R g n)
        (postnikovShiftedLayerBimodule R D n hn 1)) =
    (postnikovCellLiftCompositionMiddle R B C D P n hn b f g ≫
      postnikovPerturbedClass R D n hn) ≫ Path.diagonal R _ := by
  rw [Category.assoc, Path.diagonal_naturality, ← Category.assoc,
    postnikovCellImageComposition_middle_map]
  rfl

/-- 既存の二 ImageWitness の affine 合成を指定二経路の class 合成へ戻す全経路式。 -/
lemma postnikovCellImageComposite_map :
    (postnikovCellImageComposite R B C D P n hn b f g).hom ≫ Path.map R
      (SquareZero.baseChangeMap ((b ≫ postnikovMap R f n) ≫ postnikovMap R g n)
        (postnikovShiftedLayerBimodule R D n hn 1)) =
    (SquareZero.relativeClassComposite R (postnikovPerturbedProjection R D n hn)
      (postnikovCellLiftCompositionFirst R B C D P n hn b f g)
      (postnikovCellLiftCompositionFirst_relative R B C D P n hn b f g)
      (postnikovShiftedLayerBimodule R D n hn 1) (postnikovPerturbedClass R D n hn)
      (postnikovPerturbedClass_projection R D n hn)
      (postnikovCellLiftCompositionSecond R B C D P n hn b f g)
      (postnikovCellLiftCompositionSecond_relative R B C D P n hn b f g)).hom := by
  apply Mon.Hom.ext
  change (((postnikovCellImageForwardRelative R B C D P n hn b f g).comp
    (postnikovCellImageRelative R C D P n hn (b ≫ postnikovMap R f n) g)).hom ≫ _).hom = _
  rw [Mon.comp_hom', SquareZero.relativeClassComposite,
    SquareZero.RelativeWitness.comp_hom_linear, SquareZero.RelativeWitness.comp_hom_linear,
    add_comp, sub_comp]
  simp only [← Mon.comp_hom']
  rw [postnikovCellImageComposition_first_map, postnikovCellImageComposition_second_map,
    postnikovCellImageComposition_middle_constant_map]
  rfl

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
