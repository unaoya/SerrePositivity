module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeClassMap

/-!
概要：係数射と相対 class 経路による実模型射の合成則を構成する。
方針：第一経路を第二係数射で移して第二経路と合成し、両脚と全経路を照合する。
規約：比較経路は構成し、追加の存在仮定にしない。使われ方：Γ の実逆三角形。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Preadditive
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZeroExtension
variable {R : Type u} [CommRing R] {A W : Mon (Complex R)} {M N P : Bimod A A}
  (m : M ⟶ N) (n : N ⟶ P) (a : W ⟶ SquareZero.algebra A M)
  (b : W ⟶ SquareZero.algebra A N) (c : W ⟶ SquareZero.algebra A P) {q : W ⟶ A}
  (v : SquareZero.RelativeWitness q N (a ≫ SquareZero.coefficientMap A m) b)
  (w : SquareZero.RelativeWitness q P (b ≫ SquareZero.coefficientMap A n) c)

def composeClassWitness :
    SquareZero.RelativeWitness q P (a ≫ SquareZero.coefficientMap A (m ≫ n)) c where
  hom := ((v.mapCoefficient n).comp w).hom
  source_eq := ((v.mapCoefficient n).comp w).source_eq.trans (by
    rw [Category.assoc, SquareZero.coefficientMap_comp])
  target_eq := ((v.mapCoefficient n).comp w).target_eq
  projection_eq := ((v.mapCoefficient n).comp w).projection_eq

lemma composeClassWitness_hom_linear : (composeClassWitness m n a b c v w).hom.hom =
    (v.hom ≫ DGAlgebra.Path.map R (SquareZero.coefficientMap A n)).hom -
      ((b ≫ SquareZero.coefficientMap A n) ≫
        DGAlgebra.Path.diagonal R (SquareZero.algebra A P)).hom + w.hom.hom :=
  by
    change ((v.mapCoefficient n).comp w).hom.hom = _
    rw [SquareZero.RelativeWitness.comp_hom_linear]
    rfl

lemma classModelMap_comp : classModelMap m a b v ≫ classModelMap n b c w =
    classModelMap (m ≫ n) a c (composeClassWitness m n a b c v w) := by
  apply DGAlgebra.RelativeHomotopyPullback.hom_ext R (SquareZero.projection A P)
    c (SquareZero.zeroSection A P)
  · change (_ ≫ _) ≫ relativeLeft P c = _ ≫ relativeLeft P c
    rw [Category.assoc, classModelMap_left, classModelMap_left, classModelMap_left]
  · change (_ ≫ _) ≫ relativeRight P c = _ ≫ relativeRight P c
    rw [Category.assoc, classModelMap_right, classModelMap_right, classModelMap_right]
  · change (_ ≫ _) ≫ relativePath P c = _ ≫ relativePath P c
    apply Mon.Hom.ext
    have hp : ((classModelMap m a b v ≫ relativePath N b) ≫
        DGAlgebra.Path.map R (SquareZero.coefficientMap A n)).hom =
        ((relativeLeft M a ≫ b ≫ DGAlgebra.Path.diagonal R (SquareZero.algebra A N)).hom -
          (relativeLeft M a ≫ v.hom).hom +
          (relativePath M a ≫ DGAlgebra.Path.map R (SquareZero.coefficientMap A m)).hom) ≫
            (DGAlgebra.Path.map R (SquareZero.coefficientMap A n)).hom := by
      rw [Mon.comp_hom', classModelMap_path_linear]
    have hd : (DGAlgebra.Path.diagonal R (SquareZero.algebra A N)).hom ≫
        (DGAlgebra.Path.map R (SquareZero.coefficientMap A n)).hom =
      (SquareZero.coefficientMap A n).hom ≫
        (DGAlgebra.Path.diagonal R (SquareZero.algebra A P)).hom :=
      congrArg Mon.Hom.hom (DGAlgebra.Path.diagonal_naturality R (SquareZero.coefficientMap A n))
    have hn : (DGAlgebra.Path.map R (SquareZero.coefficientMap A (m ≫ n))).hom =
        (DGAlgebra.Path.map R (SquareZero.coefficientMap A m)).hom ≫
          (DGAlgebra.Path.map R (SquareZero.coefficientMap A n)).hom := by
      rw [← SquareZero.coefficientMap_comp, DGAlgebra.Path.map_comp]
      rfl
    rw [classModelMap_path_linear_precomp]
    simp only [← Category.assoc, classModelMap_left]
    rw [hp, classModelMap_path_linear]
    simp only [Mon.comp_hom', composeClassWitness_hom_linear, hn, comp_add, comp_sub,
      add_comp, sub_comp, Category.assoc, hd]
    abel

end SerrePositivity.KST.LocalizingInvariants.SquareZeroExtension
