module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovLayerActions
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovLayerMaps

/-!
概要：Postnikov 層の左右作用が、元の代数射と元の層比較射に対して自然であること。
方針：包含の単射性で消去し、元の代数射の積保存と層包含の自然性へ戻す。
規約：作用と比較射を選び直さない。使われ方：pro 系の係数双加群。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {B C : Mon (Complex R)}
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] (f : B ⟶ C) (n : ℤ)

lemma postnikovLayerActLeft_naturality :
    postnikovLayerActLeft R B n ≫ postnikovLayerMap R f n =
      ((postnikovMap R f (n + 1)).hom ⊗ₘ postnikovLayerMap R f n) ≫
        postnikovLayerActLeft R C n := by
  apply (cancel_mono (postnikovLayerInclusion R C n)).1
  rw [Category.assoc, postnikovLayerMap_inclusion, ← Category.assoc,
    postnikovLayerActLeft_inclusion]
  simp only [Category.assoc, postnikovLayerActLeft_inclusion, IsMonHom.mul_hom,
    ← id_tensorHom, tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id,
    ← postnikovLayerMap_inclusion]

lemma postnikovLayerActRight_naturality :
    postnikovLayerActRight R B n ≫ postnikovLayerMap R f n =
      (postnikovLayerMap R f n ⊗ₘ (postnikovMap R f (n + 1)).hom) ≫
        postnikovLayerActRight R C n := by
  apply (cancel_mono (postnikovLayerInclusion R C n)).1
  rw [Category.assoc, postnikovLayerMap_inclusion, ← Category.assoc,
    postnikovLayerActRight_inclusion]
  simp only [Category.assoc, postnikovLayerActRight_inclusion, IsMonHom.mul_hom,
    ← tensorHom_id, tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id,
    ← postnikovLayerMap_inclusion]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
