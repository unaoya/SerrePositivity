module

public import SerrePositivity.HomologicalAlgebra.NonnegativeCochainHomology
public import SerrePositivity.HomologicalAlgebra.KoszulLinearDualityNaturality
public import SerrePositivity.HomologicalAlgebra.LocalCohomology.KoszulComparison
public import Mathlib.Algebra.Homology.LocalCohomology
public import Mathlib.Algebra.Algebra.Bilinear

/-! # 局所コホモロジー上の係数の作用と零化

## 概要

非負次数の双対 Koszul コホモロジーから補次数の Tor への自然な比較を作り、R 代数 C の元による掛け算を局所コホモロジーの自己射 `localCohomologyScalarEndomorphism` として定める。双対 Koszul による局所コホモロジーの比較で係数の作用が零になる条件を段の言葉で与え、高次 Tor の零化元は低次の局所コホモロジーに零で作用することを示す。零次の局所コホモロジーはイデアルの冪ねじれである。

## 方針

Mathlib の局所コホモロジー関手には加法性・線形性の instance がないので、自己射を直接定義し、C 加群の構造は導入しない。零化は双対 Koszul の比較と Tor の比較を経由して示す。

## 規約

C の有限生成性は要求しない。

## 使われ方

`LocalCohomology/BaseChange`、CLMST の局所コホモロジーの零化。
-/

@[expose] public noncomputable section

universe u

section KoszulDualTorComparisonPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {R : Type u} [CommRing R]

/-- The integer dual of a nonpositive complex has no negative terms. -/
lemma cochainLinearDual_isZero_X_of_neg (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : ∀ q : ℤ, 0 < q → IsZero (K.X q)) (M : ModuleCat.{u} R)
    (i : ℤ) (hi : i < 0) : IsZero (((cochainLinearDualFunctor K).obj M).X i) := by
  have : Subsingleton (((cochainLinearDualFunctor K).obj M).X i) :=
    ⟨fun f g => (hK (0 - i) (by omega)).eq_of_src f g⟩
  exact ModuleCat.isZero_of_subsingleton _

/-- Ext's nonnegative dual and the integer dual compute naturally the same homology. -/
def cochainLinearDualNonnegativeHomologyNatIso (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : ∀ q : ℤ, 0 < q → IsZero (K.X q)) (n : ℕ) :
    chainLinearYonedaFunctor (toChain K) ⋙ homologyFunctor (ModuleCat R) (.up ℕ) n ≅
      cochainLinearDualFunctor K ⋙ homologyFunctor (ModuleCat R) (.up ℤ) (n : ℤ) :=
  Functor.isoWhiskerRight (cochainLinearDualNonnegativeNatIso K).symm
      (homologyFunctor (ModuleCat R) (.up ℕ) n) ≪≫
    NatIso.ofComponents (fun M => nonnegativeCochainHomologyIso
      ((cochainLinearDualFunctor K).obj M) (cochainLinearDual_isZero_X_of_neg K hK M) n)
      (fun f => nonnegativeCochainHomologyIso_hom_naturality
        ((cochainLinearDualFunctor K).map f) _ _ n)

/-- Complementary Tor computes the actual dual Koszul cohomology, naturally in coefficients. -/
def koszulDualTorComparison {e : ℕ} (z : Fin e → R) (hz : IsKoszulResolution z)
    (i : ℕ) (hi : i ≤ e) :
    koszulDualModuleFunctor z ⋙ homologyFunctor (ModuleCat.{u} R) (.up ℕ) i ≅
      (Tor (ModuleCat.{u} R) (e - i)).flip.obj
        (ModuleCat.of R (R ⧸ Ideal.span (Set.range z))) :=
  cochainLinearDualNonnegativeHomologyNatIso (koszulComplex z)
      (koszulComplex_isZero_X_of_pos z) i ≪≫
    koszulLinearDualHomologyNatIso z (i : ℤ) ≪≫
    Functor.isoWhiskerLeft (koszulModuleFunctor z)
      (eqToIso (congrArg (fun j : ℤ => homologyFunctor (ModuleCat.{u} R) (.up ℤ) j)
        (show (i : ℤ) - (e : ℤ) = -((e - i : ℕ) : ℤ) by omega))) ≪≫
    (koszulModuleTorComparison z hz (e - i)).symm

/-- Naturality reflects coefficient zero maps through the complementary Tor comparison. -/
lemma koszulDualTorComparison_map_eq_zero_iff {e : ℕ} (z : Fin e → R)
    (hz : IsKoszulResolution z) (i : ℕ) (hi : i ≤ e)
    {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    ((Tor (ModuleCat.{u} R) (e - i)).flip.obj
        (ModuleCat.of R (R ⧸ Ideal.span (Set.range z)))).map f = 0 ↔
      homologyMap ((koszulDualModuleFunctor z).map f) i = 0 := by
  let E := koszulDualTorComparison z hz i hi
  have h := E.hom.naturality f
  change homologyMap ((koszulDualModuleFunctor z).map f) i ≫ E.hom.app N =
    E.hom.app M ≫ ((Tor (ModuleCat.{u} R) (e - i)).flip.obj
      (ModuleCat.of R (R ⧸ Ideal.span (Set.range z)))).map f at h
  constructor
  · intro hf
    apply (cancel_mono (E.hom.app N)).mp
    rw [h, hf, comp_zero, zero_comp]
  · intro hf
    apply (cancel_epi (E.hom.app M)).mp
    rw [← h, hf, zero_comp, comp_zero]

/-- Higher Tor zero actions yield low-degree dual Koszul zero actions for actual multiplication. -/
lemma koszulDualHomology_coefficient_scalar_eq_zero_of_tor_annihilated
    {e : ℕ} (z : Fin e → R) (hz : IsKoszulResolution z)
    (C : Type u) [CommRing C] [Algebra R C] (I : Ideal C)
    (hTor : ∀ (N : ModuleCat.{u} R) (j : ℕ), 0 < j →
      ∀ c ∈ I, torCoefficientScalarEndomorphism C N j c = 0)
    (i : ℕ) (hi : i < e) (c : C) (hc : c ∈ I) :
    homologyMap ((koszulDualModuleFunctor z).map
      (ModuleCat.ofHom (LinearMap.mulLeft R c))) i = 0 :=
  (koszulDualTorComparison_map_eq_zero_iff z hz i (Nat.le_of_lt hi)
    (ModuleCat.ofHom (LinearMap.mulLeft R c))).mp
      (hTor _ (e - i) (Nat.sub_pos_of_lt hi) c hc)

end SerrePositivity

end KoszulDualTorComparisonPart

section LocalCohomologyActionPart

namespace SerrePositivity.HomologicalAlgebra
open CategoryTheory

variable {R : Type u} [CommRing R] (J : Ideal R) (i : ℕ)
    (C : Type u) [CommRing C] [Algebra R C]

/-- 有限性を仮定しない代数 `C` の、`J` を台とする実際の局所コホモロジー。 -/
abbrev localCohomologyModule : ModuleCat.{u} R :=
  (localCohomology J i).obj (ModuleCat.of R C)

/-- `C` の元の乗法が局所コホモロジーに誘導する具体的な自己射。 -/
def localCohomologyScalarEndomorphism (c : C) :
    localCohomologyModule J i C ⟶ localCohomologyModule J i C :=
  (localCohomology J i).map (ModuleCat.ofHom (LinearMap.mulLeft R c))

/-- 単位元の乗法から誘導される射は恒等射。 -/
@[simp] theorem localCohomologyScalarEndomorphism_one :
    localCohomologyScalarEndomorphism J i C 1 = 𝟙 _ := by
  unfold localCohomologyScalarEndomorphism
  have h : ModuleCat.ofHom (LinearMap.mulLeft R (1 : C)) = 𝟙 (ModuleCat.of R C) := by
    ext c
    simp
  rw [h]
  exact (localCohomology J i).map_id _

/-- 乗法の合成は局所コホモロジーの自己射の合成に移る。 -/
theorem localCohomologyScalarEndomorphism_mul (a b : C) :
    localCohomologyScalarEndomorphism J i C (a * b) =
      localCohomologyScalarEndomorphism J i C b ≫
        localCohomologyScalarEndomorphism J i C a := by
  unfold localCohomologyScalarEndomorphism
  rw [← Functor.map_comp]
  congr 1
  ext c
  simp

end SerrePositivity.HomologicalAlgebra

end LocalCohomologyActionPart

section KoszulLocalCohomologyActionPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {R : Type u} [CommRing R]

/-- A map killed by every stage functor is killed by their actual sequential colimit. -/
lemma sequentialFunctorColimit_map_eq_zero
    (F : ℕ ⥤ (ModuleCat.{u} R ⥤ ModuleCat.{u} R))
    {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (h : ∀ n, (F.obj n).map f = 0) : (colimit F).map f = 0 := by
  apply (isColimitOfPreserves ((evaluation (ModuleCat.{u} R) (ModuleCat.{u} R)).obj M)
    (colimit.isColimit F)).hom_ext
  intro n
  change (colimit.ι F n).app M ≫ (colimit F).map f = (colimit.ι F n).app M ≫ 0
  rw [← (colimit.ι F n).naturality f, h n, zero_comp, comp_zero]

/-- Zero maps on every finite-stage dual Koszul cohomology give zero local-cohomology maps. -/
lemma koszulLocalCohomology_map_eq_zero_of_stages [IsNoetherian R R]
    {e : ℕ} (z : Fin e → R)
    (hres : ∀ n : ℕ, IsKoszulResolution (fun j => z j ^ n)) (i : ℕ)
    {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (h : ∀ n : ℕ, homologyMap
      ((koszulDualModuleFunctor (fun j => z j ^ n)).map f) i = 0) :
    (localCohomology (Ideal.span (Set.range z)) i).map f = 0 := by
  let E := koszulDualPowerHomologyColimitNatIso z hres i
  have hf : (colimit (koszulDualPowerHomologyDiagram z i)).map f = 0 :=
    sequentialFunctorColimit_map_eq_zero _ f h
  apply (cancel_epi (E.hom.app M)).mp
  rw [← E.hom.naturality f, hf, zero_comp, comp_zero]

variable {e : ℕ} (z : Fin e → R) (i : ℕ)
    (C : Type u) [CommRing C] [Algebra R C]

/-- Finite-stage coefficient zero actions descend to the concrete local-cohomology action. -/
lemma localCohomologyScalarEndomorphism_eq_zero_of_dualKoszul_stages
    [IsNoetherian R R] (hres : ∀ n : ℕ, IsKoszulResolution (fun j => z j ^ n))
    (c : C) (h : ∀ n : ℕ, homologyMap
      ((koszulDualModuleFunctor (fun j => z j ^ n)).map
        (ModuleCat.ofHom (LinearMap.mulLeft R c))) i = 0) :
    HomologicalAlgebra.localCohomologyScalarEndomorphism
      (Ideal.span (Set.range z)) i C c = 0 :=
  koszulLocalCohomology_map_eq_zero_of_stages z hres i
    (ModuleCat.ofHom (LinearMap.mulLeft R c)) h

end SerrePositivity

end KoszulLocalCohomologyActionPart

section LocalCohomologyTorAnnihilatorPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory HomologicalComplex
variable {R : Type u} [CommRing R]

/-- Higher Tor zero actions transfer through the actual dual Koszul system to local cohomology. -/
lemma localCohomologyScalarEndomorphism_eq_zero_of_tor_annihilated
    [IsNoetherian R R] {e : ℕ} (z : Fin e → R)
    (hres : ∀ n : ℕ, IsKoszulResolution (fun j => z j ^ n))
    (C : Type u) [CommRing C] [Algebra R C] (I : Ideal C)
    (hTor : ∀ (N : ModuleCat.{u} R) (j : ℕ), 0 < j →
      ∀ c ∈ I, torCoefficientScalarEndomorphism C N j c = 0)
    (i : ℕ) (hi : i < e) (c : C) (hc : c ∈ I) :
    HomologicalAlgebra.localCohomologyScalarEndomorphism
      (Ideal.span (Set.range z)) i C c = 0 := by
  apply localCohomologyScalarEndomorphism_eq_zero_of_dualKoszul_stages z i C hres c
  intro n
  exact koszulDualHomology_coefficient_scalar_eq_zero_of_tor_annihilated
    (fun j => z j ^ n) (hres n) C I hTor i hi c hc

end SerrePositivity

end LocalCohomologyTorAnnihilatorPart

section LocalCohomologyZeroTorsionPart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex
variable {R : Type u} [CommRing R] [IsNoetherian R R] {e : ℕ} (z : Fin e → R)

/-- Mathlib's Ext-colimit local cohomology in degree zero is the actual power-torsion functor,
naturally in all coefficients and their morphisms. -/
def localCohomologyZeroPowerTorsionNatIso :
    localCohomology (Ideal.span (Set.range z)) 0 ≅
      idealPowerTorsionFunctor (Ideal.span (Set.range z)) :=
  (localCohomologyPowerKoszulIdealNatIso z 0).symm ≪≫
    (Functor.Final.colimitIso (opOp ℕ)
      (localCohomology.diagram (powerKoszulIdealDiagram z) 0)).symm ≪≫
    HasColimit.isoOfNatIso (Functor.isoWhiskerLeft
      (opOp ℕ ⋙ (localCohomology.ringModIdeals (powerKoszulIdealDiagram z)).op)
      extZeroLinearCoyonedaNatIso) ≪≫ quotientHomColimitPowerTorsionNatIso z

/-- The actual zero dual-colimit cohomology agrees with Mathlib's actual zero local cohomology. -/
def koszulDualColimitZeroLocalCohomologyNatIso :
    koszulDualColimitFunctor z ⋙ homologyFunctor (ModuleCat.{u} R) (.up ℕ) 0 ≅
      localCohomology (Ideal.span (Set.range z)) 0 :=
  koszulDualColimitZeroTorsionNatIso z ≪≫ (localCohomologyZeroPowerTorsionNatIso z).symm

end SerrePositivity

end LocalCohomologyZeroTorsionPart
