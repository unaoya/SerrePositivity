module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSourceImageExtensionSquare

/-!
概要：元の正方形に沿う源側像拡大の実代数射は、恒等・合成を厳密に保つ。
方針：元の二脚と実乗法的経路の三成分の一意性へ、三成分の関手則を渡す。
規約：同じ源側像拡大の射を使用。使われ方：実 dg 代数の図式と塔の遷移。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {B C B' C' B'' C'' : Mon (Complex R)}
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] [B'.X.IsStrictlyLE 0] [C'.X.IsStrictlyLE 0]
  [B''.X.IsStrictlyLE 0] [C''.X.IsStrictlyLE 0] (n : ℤ) (hn : 0 ≤ n)

lemma postnikovSourceImageExtensionSquareMap_id (f : B ⟶ C) :
    postnikovSourceImageExtensionSquareMap R n hn f f (𝟙 B) (𝟙 C) (by simp) = 𝟙 _ := by
  apply HomotopyPullbackModel.hom_ext R (postnikovSourceImageClass R f n hn)
    (SquareZero.zeroSection (postnikov R B n) (postnikovShiftedLayerImage R f n hn 1))
  · rw [postnikovSourceImageExtensionSquareMap_left, postnikovPerturbedMap_id,
      Category.comp_id, Category.id_comp]
  · rw [postnikovSourceImageExtensionSquareMap_right, postnikovMap_identity,
      Category.comp_id, Category.id_comp]
  · rw [postnikovSourceImageExtensionSquareMap_path, postnikovSourceImageSquareZeroMap_id,
      Path.map_id, Category.comp_id, Category.id_comp]

lemma postnikovSourceImageExtensionSquareMap_comp
    (f : B ⟶ C) (f' : B' ⟶ C') (f'' : B'' ⟶ C'')
    (s : B ⟶ B') (t : C ⟶ C') (s' : B' ⟶ B'') (t' : C' ⟶ C'')
    (h : f ≫ t = s ≫ f') (h' : f' ≫ t' = s' ≫ f'') :
    postnikovSourceImageExtensionSquareMap R n hn f f'' (s ≫ s') (t ≫ t')
      (by rw [← Category.assoc, h, Category.assoc, h', ← Category.assoc]) =
        postnikovSourceImageExtensionSquareMap R n hn f f' s t h ≫
          postnikovSourceImageExtensionSquareMap R n hn f' f'' s' t' h' := by
  apply HomotopyPullbackModel.hom_ext R (postnikovSourceImageClass R f'' n hn)
    (SquareZero.zeroSection (postnikov R B'' n) (postnikovShiftedLayerImage R f'' n hn 1))
  · rw [postnikovSourceImageExtensionSquareMap_left, Category.assoc,
      postnikovSourceImageExtensionSquareMap_left, ← Category.assoc,
      postnikovSourceImageExtensionSquareMap_left, Category.assoc, ← postnikovPerturbedMap_comp]
  · rw [postnikovSourceImageExtensionSquareMap_right, Category.assoc,
      postnikovSourceImageExtensionSquareMap_right, ← Category.assoc,
      postnikovSourceImageExtensionSquareMap_right, Category.assoc, ← postnikovMap_composition]
  · rw [postnikovSourceImageExtensionSquareMap_path, Category.assoc,
      postnikovSourceImageExtensionSquareMap_path, ← Category.assoc,
      postnikovSourceImageExtensionSquareMap_path, Category.assoc, ← Path.map_comp,
      ← postnikovSourceImageSquareZeroMap_comp]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
