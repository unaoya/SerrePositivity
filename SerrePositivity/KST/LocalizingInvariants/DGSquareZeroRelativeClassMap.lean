module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeCoefficientLaws

/-!
概要：実係数射とその像 class から標準 class への相対経路を、一つの実模型射へ組み合わせる。
方針：元の係数模型射の後に、元の相対経路による実代数同型を合成する。
規約：元の両脚と全経路の線形公式を保持。使われ方：二切断候補の実 class 射。
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
  (m : M ⟶ N) (a : W ⟶ SquareZero.algebra A M) (b : W ⟶ SquareZero.algebra A N)
  {q : W ⟶ A} (v : SquareZero.RelativeWitness q N (a ≫ SquareZero.coefficientMap A m) b)

def classModelMap : relativeModel M a ⟶ relativeModel N b :=
  coefficientModelMap m a (a ≫ SquareZero.coefficientMap A m) rfl ≫ transport N v

lemma classModelMap_left : classModelMap m a b v ≫ relativeLeft N b = relativeLeft M a := by
  rw [classModelMap, Category.assoc, transport_left, coefficientModelMap_left]

lemma classModelMap_right : classModelMap m a b v ≫ relativeRight N b = relativeRight M a := by
  rw [classModelMap, Category.assoc, transport_right, coefficientModelMap_right]

lemma classModelMap_path_linear : (classModelMap m a b v ≫ relativePath N b).hom =
    (relativeLeft M a ≫ b ≫ DGAlgebra.Path.diagonal R (SquareZero.algebra A N)).hom -
      (relativeLeft M a ≫ v.hom).hom +
        (relativePath M a ≫ DGAlgebra.Path.map R (SquareZero.coefficientMap A m)).hom := by
  rw [classModelMap, transport_path_linear_precomp]
  simp only [← Category.assoc, coefficientModelMap_left, coefficientModelMap_path]

lemma classModelMap_path_linear_precomp {T : Mon (Complex R)} (f : T ⟶ relativeModel M a) :
    ((f ≫ classModelMap m a b v) ≫ relativePath N b).hom =
      (f ≫ relativeLeft M a ≫ b ≫ DGAlgebra.Path.diagonal R (SquareZero.algebra A N)).hom -
        (f ≫ relativeLeft M a ≫ v.hom).hom +
          ((f ≫ relativePath M a) ≫ DGAlgebra.Path.map R (SquareZero.coefficientMap A m)).hom := by
  have h := congrArg (fun t => f.hom ≫ t) (classModelMap_path_linear m a b v)
  simpa only [Mon.comp_hom', comp_add, comp_sub, Category.assoc] using h

lemma classModelMap_congr {w : SquareZero.RelativeWitness q N
    (a ≫ SquareZero.coefficientMap A m) b} (h : v.hom = w.hom) :
    classModelMap m a b v = classModelMap m a b w := by
  apply DGAlgebra.RelativeHomotopyPullback.hom_ext R (SquareZero.projection A N)
    b (SquareZero.zeroSection A N)
  · change _ ≫ relativeLeft N b = _ ≫ relativeLeft N b
    rw [classModelMap_left, classModelMap_left]
  · change _ ≫ relativeRight N b = _ ≫ relativeRight N b
    rw [classModelMap_right, classModelMap_right]
  · change _ ≫ relativePath N b = _ ≫ relativePath N b
    apply Mon.Hom.ext
    rw [classModelMap_path_linear, classModelMap_path_linear, h]

lemma classModelMap_eq_coefficient (h : a ≫ SquareZero.coefficientMap A m = b)
    (hv : v.hom = b ≫ DGAlgebra.Path.diagonal R (SquareZero.algebra A N)) :
    classModelMap m a b v = coefficientModelMap m a b h := by
  apply DGAlgebra.RelativeHomotopyPullback.hom_ext R (SquareZero.projection A N)
    b (SquareZero.zeroSection A N)
  · change _ ≫ relativeLeft N b = _ ≫ relativeLeft N b
    rw [classModelMap_left, coefficientModelMap_left]
  · change _ ≫ relativeRight N b = _ ≫ relativeRight N b
    rw [classModelMap_right, coefficientModelMap_right]
  · change _ ≫ relativePath N b = _ ≫ relativePath N b
    apply Mon.Hom.ext
    rw [classModelMap_path_linear, coefficientModelMap_path, hv]
    simp only [Category.assoc, sub_self, zero_add]

end SerrePositivity.KST.LocalizingInvariants.SquareZeroExtension
