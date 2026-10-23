module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroMovingSourceOuterFaces
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroMovingSourceInnerFaces
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackPathLift

/-!
概要：右脚の底も動く source 自然性を、元の平方零 class 模型内の実経路へ移す。
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
namespace SerrePositivity.KST.LocalizingInvariants.SquareZeroExtension
open DGAlgebra
variable {R : Type u} [CommRing R] {A B T D : Mon (Complex R)} (q : A ⟶ B) (N : Bimod B B)
  (f : D ⟶ SquareZero.algebra A (bimoduleRestrict q N)) {l₀ l₁ : T ⟶ D}
  (h : DGAlgebra.Path.Witness R l₀ l₁) (r : T ⟶ DGAlgebra.Path.algebra R A) (q₀ : T ⟶ B)
  (hr : r ≫ DGAlgebra.Path.map R q = q₀ ≫ DGAlgebra.Path.diagonal R B)
  (a₀ : DGAlgebra.Path.Witness R (l₀ ≫ f)
    ((r ≫ DGAlgebra.Path.source R A) ≫ SquareZero.zeroSection A (bimoduleRestrict q N)))
  (a₁ : DGAlgebra.Path.Witness R (l₁ ≫ f)
    ((r ≫ DGAlgebra.Path.target R A) ≫ SquareZero.zeroSection A (bimoduleRestrict q N)))
  {x y : T ⟶ SquareZero.algebra B N} (v : SquareZero.RelativeWitness q₀ N x y)
  (p : SquareZero.RelativeWitness q₀ N x (q₀ ≫ SquareZero.zeroSection B N))
  (hs : (h.hom ≫ DGAlgebra.Path.map R f) ≫
    DGAlgebra.Path.map R (SquareZero.projection A (bimoduleRestrict q N)) = r)
  (hk : (h.hom ≫ DGAlgebra.Path.map R f) ≫
    DGAlgebra.Path.map R (SquareZero.baseChangeMap q N) = v.hom)
  (h₀ : a₀.hom ≫ DGAlgebra.Path.map R (SquareZero.projection A (bimoduleRestrict q N)) =
    (r ≫ DGAlgebra.Path.source R A) ≫ DGAlgebra.Path.diagonal R A)
  (k₀ : a₀.hom ≫ DGAlgebra.Path.map R (SquareZero.baseChangeMap q N) = p.hom)
  (h₁ : a₁.hom ≫ DGAlgebra.Path.map R (SquareZero.projection A (bimoduleRestrict q N)) =
    (r ≫ DGAlgebra.Path.target R A) ≫ DGAlgebra.Path.diagonal R A)
  (k₁ : a₁.hom ≫ DGAlgebra.Path.map R (SquareZero.baseChangeMap q N) = (v.reverse.comp p).hom)

def movingSourceModelHomotopy : DGAlgebra.Path.Witness R
    (HomotopyPullbackModel.lift R f (SquareZero.zeroSection A (bimoduleRestrict q N))
      l₀ (r ≫ DGAlgebra.Path.source R A) a₀)
    (HomotopyPullbackModel.lift R f (SquareZero.zeroSection A (bimoduleRestrict q N))
      l₁ (r ≫ DGAlgebra.Path.target R A) a₁) where
  hom := HomotopyPullbackModel.pathLift R f (SquareZero.zeroSection A (bimoduleRestrict q N))
    h.hom r (SquareZero.movingSourceSquare q N r q₀ hr v p)
    (SquareZero.movingSourceSquare_innerSource_eq q N r q₀ hr v p _ hs hk)
    (SquareZero.movingSourceSquare_innerTarget_zero q N r q₀ hr v p rfl)
  source_eq := by
    apply HomotopyPullbackModel.pathLift_source_eq
    · exact h.source_eq.trans (HomotopyPullbackModel.lift_left R _ _ _ _ _).symm
    · exact (HomotopyPullbackModel.lift_right R _ _ _ _ _).symm
    · exact (SquareZero.movingSourceSquare_source_eq q N r q₀ hr v p a₀.hom h₀ k₀).trans
        (HomotopyPullbackModel.lift_path R _ _ _ _ _).symm
  target_eq := by
    apply HomotopyPullbackModel.pathLift_target_eq
    · exact h.target_eq.trans (HomotopyPullbackModel.lift_left R _ _ _ _ _).symm
    · exact (HomotopyPullbackModel.lift_right R _ _ _ _ _).symm
    · exact (SquareZero.movingSourceSquare_target_eq q N r q₀ hr v p a₁.hom h₁ k₁).trans
        (HomotopyPullbackModel.lift_path R _ _ _ _ _).symm

end SerrePositivity.KST.LocalizingInvariants.SquareZeroExtension
