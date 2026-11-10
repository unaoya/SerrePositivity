module

public import SerrePositivity.BhattScholze.Almost.AlmostConnectivity
public import SerrePositivity.DifferentialGraded.Tensor.Graded
public import SerrePositivity.InfinityCategories.Derived.SemifreeBasisEquivalence
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Restriction.Completion

/-! # 完備導来テンソルの零性から almost 零性へ

## 概要
BS 著者版 Proposition 10.4 の逆方向を、導来 p 完備な複体について示す。

## 方針
半自由代表を用いて係数の短完全列から完備導来圏の三角形を作る。
核との完備テンソルが零なら、商環による作用を各コホモロジーへ移す。

## 規約
複体の有界性は仮定しない。コホモロジー次数を使う。

## 使われ方
一般の完備複体に対する almost 零性の判定。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Almost
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open InfinityCategories DerivedCompletion DifferentialGraded MonoidalCategory
open Perfectoidization.Derived
open scoped Simplicial
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

private theorem complexSemifree_kFlat {P : Complex R} (hP : complexSemifree R P) :
    complexKFlat R P :=
  moduleSemifree_objectwiseKFlat R PUnit.{1} (fun _ _ ↦ complexKFlat_unit R) hP PUnit.unit

private def completedModuleTensorUnresolvedIso (p : ℕ) (N : ModuleCat.{u} R) (M : DVertex R) :
    ((derivedInfinityHomotopyEquivalence R).functor.obj
      ⟨completedModuleTensor p R (moduleHeartVertex R N) M⟩) ≅
    (derivedComplexCompletionFunctor R (p : R)).obj
      (DerivedCategory.Q.obj ((moduleTensorCochainFunctor (M.obj 0).val).obj N)) := by
  let P := (M.obj 0).val
  let e := derivedInfinityHomotopyEquivalence R
  have := moduleFreeCochainAugmentation_quasiIso R N
  have := complexKFlat_quasiIso_left R (complexSemifree_kFlat (M.obj 0).property)
    (moduleFreeCochainAugmentation R N)
  exact e.counitIso.app _ ≪≫ (derivedComplexCompletionFunctor R (p : R)).mapIso
    (asIso (DerivedCategory.Q.map (cochainTensorMap (moduleFreeCochainAugmentation R N) (𝟙 P))) ≪≫
      DerivedCategory.Q.mapIso (cochainTensorSingleLeftIso N P))

/-- 完備導来テンソルの左入力に、古典的な商の perfectoid 化の核を置く。 -/
abbrev kernelTensor (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R]
    (hR : IsIntegralPerfectoid R p) (J : Ideal R) (M : DVertex R) : DVertex R :=
  completedModuleTensor p R (moduleHeartVertex R (ModuleCat.of R (perfectoidKernel p R hR J))) M

/-- BS 著者版 Proposition 10.4 の逆方向。核との完備テンソルの零性から almost 零性を得る。 -/
theorem isAlmostZero_of_completedTensor_isZero (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (J : Ideal R) (M : DVertex R)
    (hM : isPCompleteVertex p R M)
    (hz : IsZero ((derivedInfinityHomotopyEquivalence R).functor.obj
      ⟨kernelTensor p R hR J M⟩)) :
    IsJAlmostZero p R hR J M := by
  let K := perfectoidKernel p R hR J
  let q := Ideal.Quotient.mk K
  let P := (M.obj 0).val
  let F := derivedComplexCompletionFunctor R (p : R)
  let S := ModuleCat.shortComplexOfCompEqZero K.subtype K.mkQ
    (LinearMap.exact_subtype_mkQ K).linearMap_comp_eq_zero
  have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S
    (LinearMap.exact_subtype_mkQ K) K.injective_subtype K.mkQ_surjective
  obtain ⟨basis⟩ := complexSemifree_nonempty_basis (M.obj 0).property
  have hflat (i : ℤ) : Module.Flat R (P.X i) := by
    let := Module.Free.of_basis (basis.basis i)
    infer_instance
  have hs := moduleTensorCochain_shortExact P hflat S hS
  let triangle := F.mapTriangle.obj (DerivedCategory.triangleOfSES hs)
  have hd : triangle ∈ distTriang _ := F.map_distinguished _
    (DerivedCategory.triangleOfSES_distinguished hs)
  have hz' : IsZero triangle.obj₁ :=
    hz.of_iso (completedModuleTensorUnresolvedIso p (ModuleCat.of R K) M).symm
  have : IsIso triangle.mor₂ := (triangle.isZero₁_iff_isIso₂ hd).mp hz'
  let eR := F.mapIso (DerivedCategory.Q.mapIso (moduleTensorCochainUnitIso P)) ≪≫
    F.mapIso (derivedVertexLocalizationIso M).symm ≪≫
      (derivedComplexCompletionUnitIso R (p : R) _ hM).symm
  let B := R ⧸ K
  let X := DerivedCategory.Q.obj (baseChange q P)
  let iso := (derivedRestrictScalarsFactors q).app (baseChange q P) ≪≫
    DerivedCategory.Q.mapIso (restrictedBaseChangeComplexIso q P ≪≫
      cochainTensorSingleLeftIso (ModuleCat.of R B) P)
  let eB := (F.mapIso iso).symm ≪≫ (derivedCompletionRestrictionIso q (p : R)).app X
  let e := eR.symm ≪≫ asIso triangle.mor₂ ≪≫ eB
  intro i
  let h := (DerivedCategory.homologyFunctor (ModuleCat R) i).mapIso e ≪≫
    (derivedRestrictScalarsHomologyIso q i).app _
  apply SerrePositivity.Almost.IsAlmostZero.of_equiv h.toLinearEquiv.symm
  apply SerrePositivity.Almost.IsAlmostZero.iff_smul_eq_zero.mpr
  intro r hr x
  let y : (DerivedCategory.homologyFunctor (ModuleCat B) i).obj
      ((derivedComplexCompletionFunctor B (q (p : R))).obj X) := x
  change (Ideal.Quotient.mk K r) • y = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, zero_smul]

end SerrePositivity.BhattScholze.Almost
