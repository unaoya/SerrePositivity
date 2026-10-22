module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovLayerBase
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovLayerBimoduleMap
public import SerrePositivity.KST.LocalizingInvariants.BimoduleRestrictionSquareMap

/-!
概要：元の Postnikov 層を零切断上の実双加群にし、元の代数上の射を保持する。
方針：元の層の作用を元の代数へ制限し、その厳密集中から τ₀ へ降ろす。
規約：層を shift しない。使われ方：π₀ と高次係数を同時に保持する分裂平方零代数。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (B : Mon (Complex R)) [B.X.IsStrictlyLE 0] (n : ℤ)

attribute [local instance] layerOriginal_upperBound layerOriginal_lowerBound

def postnikovLayerZeroBimodule : Bimod (postnikov R B 0) (postnikov R B 0) :=
  postnikovBimodule R B (postnikovLayerOriginalBimodule R B n) (-(n + 1)) 0 (by omega)

lemma postnikovLayerZero_left_projection :
    ((postnikovQuotient R B 0).hom ▷ postnikovLayer R B n) ≫
      (postnikovLayerZeroBimodule R B n).actLeft =
        (postnikovLayerOriginalBimodule R B n).actLeft :=
  postnikovBimodule_left_projection R B (postnikovLayerOriginalBimodule R B n)
    (-(n + 1)) 0 (by omega)

lemma postnikovLayerZero_right_projection :
    (postnikovLayer R B n ◁ (postnikovQuotient R B 0).hom) ≫
      (postnikovLayerZeroBimodule R B n).actRight =
        (postnikovLayerOriginalBimodule R B n).actRight :=
  postnikovBimodule_right_projection R B (postnikovLayerOriginalBimodule R B n)
    (-(n + 1)) 0 (by omega)

variable {B} {C : Mon (Complex R)} [C.X.IsStrictlyLE 0] (f : B ⟶ C)

def postnikovLayerOriginalBimoduleMap : postnikovLayerOriginalBimodule R B n ⟶
    bimoduleRestrict f (postnikovLayerOriginalBimodule R C n) :=
  bimoduleRestrictSquareMap (postnikovQuotient R B (n + 1))
    (postnikovQuotient R C (n + 1)) f (postnikovMap R f (n + 1))
    (postnikovQuotient_naturality R f (n + 1)) (postnikovLayerBimoduleMap R f n)

lemma postnikovLayerOriginalBimoduleMap_hom :
    (postnikovLayerOriginalBimoduleMap R n f).hom = postnikovLayerMap R f n := rfl

lemma postnikovLayerOriginal_left_naturality :
    (postnikovLayerOriginalBimodule R B n).actLeft ≫ postnikovLayerMap R f n =
      (f.hom ⊗ₘ postnikovLayerMap R f n) ≫
        (postnikovLayerOriginalBimodule R C n).actLeft := by
  have h := (postnikovLayerOriginalBimoduleMap R n f).left_act_hom
  change (postnikovLayerOriginalBimodule R B n).actLeft ≫ postnikovLayerMap R f n =
    (B.X ◁ postnikovLayerMap R f n) ≫ (f.hom ▷ postnikovLayer R C n) ≫
      (postnikovLayerOriginalBimodule R C n).actLeft at h
  rw [← tensorHom_def'_assoc] at h
  exact h

lemma postnikovLayerOriginal_right_naturality :
    (postnikovLayerOriginalBimodule R B n).actRight ≫ postnikovLayerMap R f n =
      (postnikovLayerMap R f n ⊗ₘ f.hom) ≫
        (postnikovLayerOriginalBimodule R C n).actRight := by
  have h := (postnikovLayerOriginalBimoduleMap R n f).right_act_hom
  change (postnikovLayerOriginalBimodule R B n).actRight ≫ postnikovLayerMap R f n =
    (postnikovLayerMap R f n ▷ B.X) ≫ (postnikovLayer R C n ◁ f.hom) ≫
      (postnikovLayerOriginalBimodule R C n).actRight at h
  rw [← tensorHom_def_assoc] at h
  exact h

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
