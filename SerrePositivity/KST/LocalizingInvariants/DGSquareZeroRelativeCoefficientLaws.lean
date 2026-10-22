module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeCoefficientMap

/-!
概要：底を固定した係数模型射は、元の係数射の恒等と合成を厳密に保つ。
方針：元の両脚と Path.map の恒等・合成則を三成分の一意性へ渡す。
規約：class の可換式は指定した元の端点に対して入力する。使われ方：Γ の逆三角形。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZeroExtension
variable {R : Type u} [CommRing R] {A W : Mon (Complex R)} {M N P : Bimod A A}

lemma coefficientModelMap_comp (m : M ⟶ N) (n : N ⟶ P)
    (a : W ⟶ SquareZero.algebra A M) (b : W ⟶ SquareZero.algebra A N)
    (c : W ⟶ SquareZero.algebra A P)
    (ha : a ≫ SquareZero.coefficientMap A m = b) (hb : b ≫ SquareZero.coefficientMap A n = c) :
    coefficientModelMap m a b ha ≫ coefficientModelMap n b c hb =
      coefficientModelMap (m ≫ n) a c (by
        rw [← SquareZero.coefficientMap_comp, ← Category.assoc, ha, hb]) := by
  apply DGAlgebra.RelativeHomotopyPullback.hom_ext R (SquareZero.projection A P)
    c (SquareZero.zeroSection A P)
  · change (_ ≫ _) ≫ relativeLeft P c = _ ≫ relativeLeft P c
    rw [Category.assoc, coefficientModelMap_left,
      coefficientModelMap_left, coefficientModelMap_left]
  · change (_ ≫ _) ≫ relativeRight P c = _ ≫ relativeRight P c
    rw [Category.assoc, coefficientModelMap_right,
      coefficientModelMap_right, coefficientModelMap_right]
  · change (_ ≫ _) ≫ relativePath P c = _ ≫ relativePath P c
    rw [Category.assoc, coefficientModelMap_path, ← Category.assoc, coefficientModelMap_path,
      Category.assoc, ← DGAlgebra.Path.map_comp, SquareZero.coefficientMap_comp,
      coefficientModelMap_path]

lemma coefficientModelMap_id (a : W ⟶ SquareZero.algebra A M) :
    coefficientModelMap (𝟙 M) a a (by rw [SquareZero.coefficientMap_id, Category.comp_id]) =
      𝟙 (relativeModel M a) := by
  apply DGAlgebra.RelativeHomotopyPullback.hom_ext R (SquareZero.projection A M)
    a (SquareZero.zeroSection A M)
  · change _ ≫ relativeLeft M a = _ ≫ relativeLeft M a
    rw [coefficientModelMap_left, Category.id_comp]
  · change _ ≫ relativeRight M a = _ ≫ relativeRight M a
    rw [coefficientModelMap_right, Category.id_comp]
  · change _ ≫ relativePath M a = _ ≫ relativePath M a
    rw [coefficientModelMap_path, SquareZero.coefficientMap_id,
      DGAlgebra.Path.map_id, Category.comp_id, Category.id_comp]

end SerrePositivity.KST.LocalizingInvariants.SquareZeroExtension
