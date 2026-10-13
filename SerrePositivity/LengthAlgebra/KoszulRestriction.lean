module

public import SerrePositivity.HomologicalAlgebra.KoszulRestriction
public import SerrePositivity.PerfectComplex.NormalizedLengthComap

/-! # 代数を係数とする Koszul ホモロジーの長さと係数制限

代数の通常の作用と、環準同型から構成した作用を具体的な線形同型で比較する。
二段の係数制限による長さと、係数代数上の Koszul ホモロジーの長さは一致する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
open CategoryTheory
set_option backward.isDefEq.respectTransparency false

/-- 代数作用から作った係数加群と、環準同型による係数制限の作用を明示的に比較。 -/
def koszulModuleAlgebraHomologyIso
    {S C : Type u} [CommRing S] [CommRing C] [Algebra S C]
    {r : ℕ} (z : Fin r → S) (q : ℤ) :
    ((koszulModuleFunctor z).obj (ModuleCat.of S C)).homology q ≅
      (ModuleCat.restrictScalars (algebraMap S C)).obj
        ((koszulComplex (algebraMap S C ∘ z)).homology q) := by
  let ec : ModuleCat.of S C ≅
      (ModuleCat.restrictScalars (algebraMap S C)).obj (ModuleCat.of C C) :=
    LinearEquiv.toModuleIso
      (X₁ := ModuleCat.of S C)
      (X₂ := (ModuleCat.restrictScalars (algebraMap S C)).obj (ModuleCat.of C C))
      { toFun := fun x ↦ x
        invFun := fun x ↦ x
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun a x ↦ by
          change a • x = algebraMap S C a * x
          exact Algebra.smul_def a x }
  exact (HomologicalComplex.homologyFunctor _ _ q).mapIso
    ((koszulModuleFunctor z).mapIso ec) ≪≫
    koszulModuleHomologyIso (algebraMap S C) z q

/-- 係数加群の Koszul ホモロジーを二段の係数制限で測る長さは、
係数代数上の Koszul ホモロジーを直接測る長さと一致する。 -/
theorem length_comap_koszulModuleHomology
    {R S C : Type u} [CommRing R] [CommRing S] [CommRing C]
    [Algebra R S] [Algebra S C] [Algebra R C] [IsScalarTower R S C]
    {J : Ideal R} (lam : NormalizedLength R J) (K : Ideal S)
    (hK : J.map (algebraMap R S) ≤ K) {r : ℕ} (z : Fin r → S) (q : ℤ) :
    (lam.comap (algebraMap R S) K hK).len
      (((koszulModuleFunctor z).obj (ModuleCat.of S C)).homology q) =
    (let _ := Module.compHom ((koszulComplex (algebraMap S C ∘ z)).homology q)
      (algebraMap R C)
     lam.len ((koszulComplex (algebraMap S C ∘ z)).homology q)) := by
  let β := algebraMap S C
  let φ := algebraMap R S
  let X := ((koszulModuleFunctor z).obj (ModuleCat.of S C)).homology q
  let H := (koszulComplex (β ∘ z)).homology q
  let e : (ModuleCat.restrictScalars φ).obj X ≅
      (ModuleCat.restrictScalars (algebraMap R C)).obj H :=
    (ModuleCat.restrictScalars φ).mapIso (koszulModuleAlgebraHomologyIso z q) ≪≫
      (ModuleCat.restrictScalarsComp'App φ β (algebraMap R C)
        (IsScalarTower.algebraMap_eq R S C) H).symm
  let := Module.compHom X φ
  let := Module.compHom H (algebraMap R C)
  exact lam.len_congr _ _ e.toLinearEquiv

end SerrePositivity
