module

public import SerrePositivity.HomologicalAlgebra.Ext.LocalCohomology
public import SerrePositivity.HomologicalAlgebra.LocalCohomology.Actions
public import SerrePositivity.HomologicalAlgebra.TorCoefficientIdeal
public import SerrePositivity.CommutativeAlgebra.SystemOfParameters.Finite

/-! # 局所コホモロジーのスカラー作用の環の変更と極大台での零化

## 概要

代数の塔に沿った係数の制限の同型と掛け算の両立から、局所コホモロジーのスカラー自己射の零化が環の変更で保たれることを示し、極大イデアルを台とする低次の局所コホモロジーが高次 Tor の零化元（底のイデアルの Tor の零化元を含む）で零化されることを与える。

## 方針

環の変更での比較は HomologicalAlgebra/Ext/LocalCohomology の一般の Noether 係数環の変更の同型による。

## 規約

KoszulDualBaseChange は Ext/LocalCohomology が import するので別ファイルのまま。

## 使われ方

CLMST の局所コホモロジーの消滅と命題 2.4.7 の周辺。
-/

@[expose] public noncomputable section

universe u

section LocalCohomologyScalarBaseChangePart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
variable {R S C : Type u} [CommRing R] [CommRing S] [CommRing C]
variable [Algebra R S] [Algebra S C] [Algebra R C] [IsScalarTower R S C]

/-- Identify the restricted coefficient algebra with its given base-ring module,
using the actual algebra tower. -/
def algebraTowerCoefficientRestrictIso :
    (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S C) ≅ ModuleCat.of R C :=
  (LinearEquiv.toModuleIso
    (X₁ := ModuleCat.of R C)
    (X₂ := (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S C))
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => by
        change (r • (x : C) : C) = (algebraMap R S r) • (x : C)
        simp only [Algebra.smul_def]
        rw [IsScalarTower.algebraMap_apply R S C r] }).symm

/-- Multiplication by a coefficient algebra element respects the actual module identification. -/
lemma algebraTowerCoefficientRestrictIso_mul (c : C) :
    (ModuleCat.restrictScalars (algebraMap R S)).map
        (ModuleCat.ofHom (LinearMap.mulLeft S c)) ≫
        (algebraTowerCoefficientRestrictIso (R := R) (S := S) (C := C)).hom =
      (algebraTowerCoefficientRestrictIso (R := R) (S := S) (C := C)).hom ≫
        ModuleCat.ofHom (LinearMap.mulLeft R c) := by
  ext x
  rfl

/-- The concrete scalar endomorphisms used in the paper vanish over one
coefficient ring exactly when they vanish over the other, in every degree. -/
lemma localCohomologyScalarEndomorphism_ring_change_eq_zero_iff
    [IsNoetherianRing R] [IsNoetherianRing S] {e : ℕ} (z : Fin e → R) (J : Ideal S)
    (h : ((Ideal.span (Set.range z)).map (algebraMap R S)).radical = J.radical)
    (i : ℕ) (c : C) :
    HomologicalAlgebra.localCohomologyScalarEndomorphism (Ideal.span (Set.range z)) i C c = 0 ↔
      HomologicalAlgebra.localCohomologyScalarEndomorphism J i C c = 0 := by
  let U := ModuleCat.restrictScalars (algebraMap R S)
  let F := localCohomology (Ideal.span (Set.range z)) i
  let E := algebraTowerCoefficientRestrictIso (R := R) (S := S) (C := C)
  let f : ModuleCat.of S C ⟶ ModuleCat.of S C := ModuleCat.ofHom (LinearMap.mulLeft S c)
  let g : ModuleCat.of R C ⟶ ModuleCat.of R C := ModuleCat.ofHom (LinearMap.mulLeft R c)
  have hw : F.map (U.map f) ≫ (F.mapIso E).hom = (F.mapIso E).hom ≫ F.map g := by
    change F.map (U.map f) ≫ F.map E.hom = F.map E.hom ≫ F.map g
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    exact congrArg F.map (algebraTowerCoefficientRestrictIso_mul (R := R) (S := S) c)
  have hzero : F.map (U.map f) = 0 ↔ F.map g = 0 := by
    constructor
    · intro hf
      apply (cancel_epi (F.mapIso E).hom).mp
      simpa only [hf, zero_comp, comp_zero] using hw.symm
    · intro hg
      apply (cancel_mono (F.mapIso E).hom).mp
      simpa only [hg, zero_comp, comp_zero] using hw
  exact hzero.symm.trans
    (localCohomologyRestrictScalarsSupport_map_eq_zero_iff z (algebraMap R S) J h i f)

end SerrePositivity

end LocalCohomologyScalarBaseChangePart

section ParameterLocalCohomologyAnnihilatorPart

namespace SerrePositivity
open CategoryTheory
variable {R D C : Type u} [CommRing R] [CommRing D] [CommRing C]
variable [IsNoetherianRing R] [IsNoetherianRing D] [IsLocalRing D]
variable [Algebra R D] [Algebra D C] [Algebra R C] [IsScalarTower R D C]

/-- Parameter support and actual ring change transfer higher Tor annihilators
to low local cohomology at the maximal ideal, without regularity over D. -/
lemma parameterLocalCohomologyScalarEndomorphism_eq_zero_of_tor_annihilated
    {e : ℕ} (z : Fin e → R)
    (hz : IsSystemOfParameters D (algebraMap R D ∘ z))
    (hres : ∀ n : ℕ, IsKoszulResolution (fun j => z j ^ n))
    (I : Ideal C)
    (hTor : ∀ (N : ModuleCat.{u} R) (j : ℕ), 0 < j →
      ∀ c ∈ I, torCoefficientScalarEndomorphism C N j c = 0)
    (i : ℕ) (hi : i < e) (c : C) (hc : c ∈ I) :
    HomologicalAlgebra.localCohomologyScalarEndomorphism
      (IsLocalRing.maximalIdeal D) i C c = 0 := by
  have hrad : ((Ideal.span (Set.range z)).map (algebraMap R D)).radical =
      (IsLocalRing.maximalIdeal D).radical := by
    rw [Ideal.map_span, ← Set.range_comp, hz.2,
      Ideal.IsPrime.radical (inferInstance : (IsLocalRing.maximalIdeal D).IsPrime)]
  apply (localCohomologyScalarEndomorphism_ring_change_eq_zero_iff
    (S := D) z (IsLocalRing.maximalIdeal D) hrad i c).mp
  exact localCohomologyScalarEndomorphism_eq_zero_of_tor_annihilated
    z hres C I hTor i hi c hc

/-- The original base ideal suffices; the established Tor image-ideal theorem
supplies the full coefficient-ring ideal used in the local cohomology argument. -/
lemma parameterLocalCohomologyScalarEndomorphism_eq_zero_of_baseIdeal_tor
    {S : Type u} [CommRing S] (ψ : S →+* C) (I : Ideal S)
    {e : ℕ} (z : Fin e → R)
    (hz : IsSystemOfParameters D (algebraMap R D ∘ z))
    (hres : ∀ n : ℕ, IsKoszulResolution (fun j => z j ^ n))
    (hTor : ∀ (N : ModuleCat.{u} R) (j : ℕ), 0 < j →
      ∀ s ∈ I, torCoefficientScalarEndomorphism C N j (ψ s) = 0)
    (i : ℕ) (hi : i < e) (s : S) (hs : s ∈ I) :
    HomologicalAlgebra.localCohomologyScalarEndomorphism
      (IsLocalRing.maximalIdeal D) i C (ψ s) = 0 := by
  apply parameterLocalCohomologyScalarEndomorphism_eq_zero_of_tor_annihilated
    z hz hres (I.map ψ) ?_ i hi (ψ s) (Ideal.mem_map_of_mem ψ hs)
  intro N j hj
  exact torCoefficientScalarEndomorphism_mapIdeal_eq_zero ψ I N j (hTor N j hj)

end SerrePositivity

end ParameterLocalCohomologyAnnihilatorPart
