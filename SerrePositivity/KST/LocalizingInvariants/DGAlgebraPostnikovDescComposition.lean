module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTransition

/-!
概要：元の代数射の有限切断への降下は、前合成と後合成を厳密に保持する。
方針：元の商射の全射性と降下の回収式を使う。
規約：元の代数射の等式として提供。使われ方：元の roof の零切断の三角形。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {A B C D : Mon (Complex R)}
  [A.X.IsStrictlyLE 0] [B.X.IsStrictlyLE 0] (n : ℤ)
  [C.X.IsStrictlyGE (-n)] [D.X.IsStrictlyGE (-n)]

lemma postnikovDesc_precompose (u : A ⟶ B) (g : B ⟶ C) :
    postnikovMap R u n ≫ postnikovDesc R n g = postnikovDesc R n (u ≫ g) := by
  apply postnikovQuotient_cancel R A n
  rw [← Category.assoc, postnikovQuotient_naturality, Category.assoc,
    postnikovQuotient_desc, postnikovQuotient_desc]

lemma postnikovDesc_postcompose (g : B ⟶ C) (v : C ⟶ D) :
    postnikovDesc R n g ≫ v = postnikovDesc R n (g ≫ v) := by
  apply postnikovQuotient_cancel R B n
  rw [← Category.assoc, postnikovQuotient_desc, postnikovQuotient_desc]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
