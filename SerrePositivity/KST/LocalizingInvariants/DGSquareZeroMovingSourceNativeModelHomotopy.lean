module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroMovingSourceNativeFaces
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitnessCoefficient
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackPathLift

/-!
概要：動く底の source 自然性を、元の native 係数の class 模型内へ戻す。
方針：零底の sourceSlide と指定底経路を同時に持ち上げ、元の全四辺で path lift する。
規約：始点・終点の全 class 経路の射影式を使用。使われ方：W の模型比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero
variable {R : Type u} [CommRing R] {A B T : Mon (Complex R)} (q : A ⟶ B) (N : Bimod B B)
  {M : Bimod A A} (e : M ≅ bimoduleRestrict q N)
  (r : T ⟶ DGAlgebra.Path.algebra R A) (q₀ : T ⟶ B)
  (hr : r ≫ DGAlgebra.Path.map R q = q₀ ≫ DGAlgebra.Path.diagonal R B)
  {x y z : T ⟶ algebra B N} (v : RelativeWitness q₀ N x y) (p : RelativeWitness q₀ N x z)

lemma movingSourceNativeSquare_innerTarget_zero (hz : z = q₀ ≫ zeroSection B N) :
    movingSourceNativeSquare q N e r q₀ hr v p ≫
      DGAlgebra.Path.map R (DGAlgebra.Path.target R (algebra A M)) =
    r ≫ DGAlgebra.Path.map R (zeroSection A M) := by
  apply movingSourceNativeSquare_innerTarget
  · rw [Category.assoc, ← DGAlgebra.Path.map_comp, zeroSection_projection,
      DGAlgebra.Path.map_id, Category.comp_id]
  · have hk : zeroSection A M ≫ ((coefficientIso A e).hom ≫ baseChangeMap q N) =
        q ≫ zeroSection B N := by
      rw [← Category.assoc, coefficientIso_hom, zeroSection_coefficientMap]
      exact zeroSection_mapOver q (bimoduleRestrict q N) N (𝟙 _)
    rw [Category.assoc, ← DGAlgebra.Path.map_comp, hk, DGAlgebra.Path.map_comp,
      ← Category.assoc, hr, Category.assoc, DGAlgebra.Path.diagonal_naturality, hz,
      Category.assoc]

end SerrePositivity.KST.LocalizingInvariants.SquareZero

namespace SerrePositivity.KST.LocalizingInvariants.SquareZeroExtension
open DGAlgebra
variable {R : Type u} [CommRing R] {A B T D : Mon (Complex R)} (q : A ⟶ B) (N : Bimod B B)
  {M : Bimod A A} (e : M ≅ bimoduleRestrict q N)
  (f : D ⟶ SquareZero.algebra A M) {l₀ l₁ : T ⟶ D}
  (h : DGAlgebra.Path.Witness R l₀ l₁) (r : T ⟶ DGAlgebra.Path.algebra R A) (q₀ : T ⟶ B)
  (hr : r ≫ DGAlgebra.Path.map R q = q₀ ≫ DGAlgebra.Path.diagonal R B)
  (a₀ : DGAlgebra.Path.Witness R (l₀ ≫ f)
    ((r ≫ DGAlgebra.Path.source R A) ≫ SquareZero.zeroSection A M))
  (a₁ : DGAlgebra.Path.Witness R (l₁ ≫ f)
    ((r ≫ DGAlgebra.Path.target R A) ≫ SquareZero.zeroSection A M))
  {x y : T ⟶ SquareZero.algebra B N} (v : SquareZero.RelativeWitness q₀ N x y)
  (p : SquareZero.RelativeWitness q₀ N x (q₀ ≫ SquareZero.zeroSection B N))
  (hs : (h.hom ≫ DGAlgebra.Path.map R f) ≫
    DGAlgebra.Path.map R (SquareZero.projection A M) = r)
  (hk : (h.hom ≫ DGAlgebra.Path.map R f) ≫
    DGAlgebra.Path.map R ((SquareZero.coefficientIso A e).hom ≫
      SquareZero.baseChangeMap q N) = v.hom)
  (h₀ : a₀.hom ≫ DGAlgebra.Path.map R (SquareZero.projection A M) =
    (r ≫ DGAlgebra.Path.source R A) ≫ DGAlgebra.Path.diagonal R A)
  (k₀ : a₀.hom ≫ DGAlgebra.Path.map R ((SquareZero.coefficientIso A e).hom ≫
    SquareZero.baseChangeMap q N) = p.hom)
  (h₁ : a₁.hom ≫ DGAlgebra.Path.map R (SquareZero.projection A M) =
    (r ≫ DGAlgebra.Path.target R A) ≫ DGAlgebra.Path.diagonal R A)
  (k₁ : a₁.hom ≫ DGAlgebra.Path.map R ((SquareZero.coefficientIso A e).hom ≫
    SquareZero.baseChangeMap q N) = (v.reverse.comp p).hom)

def movingSourceNativeModelHomotopy : DGAlgebra.Path.Witness R
    (HomotopyPullbackModel.lift R f (SquareZero.zeroSection A M)
      l₀ (r ≫ DGAlgebra.Path.source R A) a₀)
    (HomotopyPullbackModel.lift R f (SquareZero.zeroSection A M)
      l₁ (r ≫ DGAlgebra.Path.target R A) a₁) where
  hom := HomotopyPullbackModel.pathLift R f (SquareZero.zeroSection A M)
    h.hom r (SquareZero.movingSourceNativeSquare q N e r q₀ hr v p)
    (SquareZero.movingSourceNativeSquare_innerSource q N e r q₀ hr v p _ hs hk)
    (SquareZero.movingSourceNativeSquare_innerTarget_zero q N e r q₀ hr v p rfl)
  source_eq := by
    apply HomotopyPullbackModel.pathLift_source_eq
    · exact h.source_eq.trans (HomotopyPullbackModel.lift_left R _ _ _ _ _).symm
    · exact (HomotopyPullbackModel.lift_right R _ _ _ _ _).symm
    · exact (SquareZero.movingSourceNativeSquare_source q N e r q₀ hr v p a₀.hom h₀ k₀).trans
        (HomotopyPullbackModel.lift_path R _ _ _ _ _).symm
  target_eq := by
    apply HomotopyPullbackModel.pathLift_target_eq
    · exact h.target_eq.trans (HomotopyPullbackModel.lift_left R _ _ _ _ _).symm
    · exact (HomotopyPullbackModel.lift_right R _ _ _ _ _).symm
    · exact (SquareZero.movingSourceNativeSquare_target q N e r q₀ hr v p a₁.hom h₁ k₁).trans
        (HomotopyPullbackModel.lift_path R _ _ _ _ _).symm

end SerrePositivity.KST.LocalizingInvariants.SquareZeroExtension
