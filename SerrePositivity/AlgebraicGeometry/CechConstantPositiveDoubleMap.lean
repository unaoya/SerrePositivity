module

public import SerrePositivity.AlgebraicGeometry.CechConstantPositiveDouble

/-!
概要：同じ定数列の正次数の商に、元の複体の射を渡す。
方針：外零次の零複体の恒等と、正次数の元の射を使う。
規約：同じ項・微分と係数の宇宙を保つ。
使われ方：F8の基底列の短完全列と核の比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u v
variable {R : Type v} [CommRing R]
variable {A B : CochainComplex (ModuleCat.{u} R) ℕ}

/-- 同じ正次数の商の射の各外次数の成分。 -/
def cechConstantPositiveDoubleMapComponent (f : A ⟶ B) :
    ∀ n, (cechConstantPositiveDouble A).X n ⟶ (cechConstantPositiveDouble B).X n
  | 0 => 𝟙 (HomologicalComplex.zero : CochainComplex (ModuleCat.{u} R) ℕ)
  | _ + 1 => f

set_option backward.isDefEq.respectTransparency false in
/-- 元の複体の射から、同じ正次数の商の二重複体の射を得る。 -/
def cechConstantPositiveDoubleMap (f : A ⟶ B) :
    cechConstantPositiveDouble A ⟶ cechConstantPositiveDouble B :=
  CochainComplex.ofHom (cechConstantPositiveDoubleMapComponent f) (by
    intro n
    cases n with
    | zero =>
      change 𝟙 _ ≫ (cechConstantPositiveDouble B).d 0 1 =
        (cechConstantPositiveDouble A).d 0 1 ≫ f
      have hA : (cechConstantPositiveDouble A).d 0 1 = 0 :=
        CochainComplex.of_d (cechConstantPositiveDoubleTerm A) (cechConstantPositiveDoubleD A) 0
      have hB : (cechConstantPositiveDouble B).d 0 1 = 0 :=
        CochainComplex.of_d (cechConstantPositiveDoubleTerm B) (cechConstantPositiveDoubleD B) 0
      rw [hA, hB, comp_zero, zero_comp]
    | succ n =>
      change f ≫ (cechConstantPositiveDouble B).d (n + 1) (n + 2) =
        (cechConstantPositiveDouble A).d (n + 1) (n + 2) ≫ f
      have hA : (cechConstantPositiveDouble A).d (n + 1) (n + 2) =
          (cechConstantCochainComplex A).d (n + 1) (n + 2) := CochainComplex.of_d _ _ _
      have hB : (cechConstantPositiveDouble B).d (n + 1) (n + 2) =
          (cechConstantCochainComplex B).d (n + 1) (n + 2) := CochainComplex.of_d _ _ _
      have h : f ≫ (cechConstantCochainComplex B).d (n + 1) (n + 2) =
          (cechConstantCochainComplex A).d (n + 1) (n + 2) ≫ f :=
        ((AlgebraicTopology.alternatingCofaceMapComplex (CochainComplex (ModuleCat.{u} R) ℕ)).map
          ((Functor.const SimplexCategory).map f)).comm (n + 1) (n + 2)
      exact (congrArg (fun g ↦ f ≫ g) hB).trans
        (h.trans (congrArg (fun g ↦ g ≫ f) hA).symm))

end SerrePositivity.AlgebraicGeometry
