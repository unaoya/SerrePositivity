module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeClassComposition

/-!
概要：実 class 模型射の後の相対輸送は、指定 class 経路の実合成に一致する。
方針：元の両脚と全経路の線形公式により、三成分の一意性で比較する。
規約：係数射と源は固定。使われ方：元の class 経路と coherent な貼合せの差の補正。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Preadditive
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZeroExtension
variable {R : Type u} [CommRing R] {A W : Mon (Complex R)} {M N : Bimod A A}
  (m : M ⟶ N) (a : W ⟶ SquareZero.algebra A M)
  (b c : W ⟶ SquareZero.algebra A N) {q : W ⟶ A}
  (v : SquareZero.RelativeWitness q N (a ≫ SquareZero.coefficientMap A m) b)
  (w : SquareZero.RelativeWitness q N b c)

lemma classModelMap_postTransport : classModelMap m a b v ≫ transport N w =
    classModelMap m a c (v.comp w) := by
  apply DGAlgebra.RelativeHomotopyPullback.hom_ext R (SquareZero.projection A N)
    c (SquareZero.zeroSection A N)
  · change (_ ≫ _) ≫ relativeLeft N c = _ ≫ relativeLeft N c
    rw [Category.assoc, transport_left, classModelMap_left, classModelMap_left]
  · change (_ ≫ _) ≫ relativeRight N c = _ ≫ relativeRight N c
    rw [Category.assoc, transport_right, classModelMap_right, classModelMap_right]
  · change (_ ≫ _) ≫ relativePath N c = _ ≫ relativePath N c
    apply Mon.Hom.ext
    rw [transport_path_linear_precomp]
    simp only [← Category.assoc, classModelMap_left]
    rw [classModelMap_path_linear, classModelMap_path_linear]
    simp only [Mon.comp_hom', SquareZero.RelativeWitness.comp_hom_linear,
      comp_add, comp_sub, Category.assoc]
    abel

end SerrePositivity.KST.LocalizingInvariants.SquareZeroExtension
