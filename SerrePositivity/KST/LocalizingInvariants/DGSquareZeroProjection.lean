module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroAlgebra

/-!
概要：分裂平方零 dg 代数の射影・標準切断と、実 kernel の表示を供給する。
方針：四つの積成分を使い、直和の射影と包含を実代数射にする。
規約：双加群の包含は chain map。使われ方：derivation を代数的切断に同定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory
open scoped MonObj
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero
variable {R : Type u} [CommRing R] (A : Mon (Complex R)) (M : Bimod A A)

def projection : algebra A M ⟶ A :=
  Mon.Hom.mk' biprod.fst (by
    change (η[A.X] ≫ biprod.inl) ≫ biprod.fst = η[A.X]
    rw [Category.assoc, biprod.inl_fst, Category.comp_id]) (_root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul_fst A M)

def zeroSection : A ⟶ algebra A M :=
  Mon.Hom.mk' biprod.inl rfl (_root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul_ll A M).symm

lemma zeroSection_projection : zeroSection A M ≫ projection A M = 𝟙 A := by
  apply Mon.Hom.ext
  exact biprod.inl_fst

def idealInclusion : M.X ⟶ (algebra A M).X := biprod.inr

lemma idealInclusion_projection : idealInclusion A M ≫ (projection A M).hom = 0 :=
  biprod.inr_fst

def idealKernelFork : KernelFork (projection A M).hom :=
  KernelFork.ofι (idealInclusion A M) (idealInclusion_projection A M)

def idealKernelFork_isLimit : IsLimit (idealKernelFork A M) :=
  biprod.isKernelFstKernelFork A.X M.X

lemma idealInclusion_square_zero :
    (idealInclusion A M ⊗ₘ idealInclusion A M) ≫ μ[(algebra A M).X] = 0 :=
  _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul_rr A M

end SerrePositivity.KST.LocalizingInvariants.SquareZero
