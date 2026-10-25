module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompleteScalarConePurity
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.BoundedAboveCompletionEquivalence
public import SerrePositivity.HomologicalAlgebra.FaithfullyFlatDerivedHomology
public import SerrePositivity.HomologicalAlgebra.TorBaseChange
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Flat.Localization

/-!
# 完備化と冪ねじれによる負次数消滅の検出

## 概要
BS Rem 7.15（著者版 p.62）の raw 源を、完備化と局所化から比較するための判定。

## 方針
完備化単位の Koszul 同値性により、負次数ホモロジーの分母作用は単射になる。
各元の分母冪ねじれと合わせて消滅させる。

## 規約
元の導来対象を用いる。環の正則性・有界ねじれ・対象の完備性は仮定しない。

## 使われ方
raw 源の局所化側で得られる冪ねじれ性と、既証明の完備化純性を接続する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits HomologicalComplex DerivedCompletion
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R] (a : R)

/-- 概要：隣接する二次数の消滅は、実スカラー錐の中間ホモロジーを消す。
方針：実写像錐の長完全列を任意の複体モデルで使う。
規約：対象の完備性は不要。
使われ方：BS Rem 7.15（著者版 p.62）の完備化側の消滅。 -/
theorem unconditionalScalarCone_homology_isZero
    (X : ConcreteDerivedCategory R) (i : ℤ)
    (hi : IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj X))
    (hi1 : IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) (i + 1)).obj X)) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj
      ((derivedScalarConeFunctor R a).obj X)) := by
  let K := DerivedCategory.Q.objPreimage X
  let eX := DerivedCategory.Q.objObjPreimageIso X
  have hK (n : ℤ) (hn : IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) n).obj X)) :
      IsZero (K.homology n) :=
    hn.of_iso (((DerivedCategory.homologyFunctorFactors (ModuleCat R) n).app K).symm ≪≫
      (DerivedCategory.homologyFunctor (ModuleCat R) n).mapIso eX)
  have hc : IsZero (((scalarConeFunctor a).obj K).homology i) :=
    (Cone.exact₃ (smulId a K) i (i + 1) rfl).isZero_X₂
      ((hK i hi).eq_zero_of_src _) ((hK (i + 1) hi1).eq_zero_of_tgt _)
  let ec := ((DerivedCategory.homologyFunctorFactors (ModuleCat R) i).app
      ((scalarConeFunctor a).obj K)).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat R) i).mapIso
      ((derivedScalarConeComparison R a).symm.app K ≪≫
        (derivedScalarConeFunctor R a).mapIso eX)
  exact hc.of_iso ec.symm

/-- 概要：完備化に負次数ホモロジーがなければ、元の負次数の分母作用は単射。
方針：完備化単位のスカラー錐上の同型と長完全列を使う。
規約：元の対象が完備である必要はない。
使われ方：BS Rem 7.15（著者版 p.62）の局所化側の冪ねじれとの接続。 -/
theorem unconditionalNegativeHomology_smul_injective_of_completion_isGE
    (X : ConcreteDerivedCategory R)
    (hX : ((derivedComplexCompletionFunctor R a).obj X).IsGE 0)
    (i : ℤ) (hi : i < 0) :
    Function.Injective
      (fun x : (DerivedCategory.homologyFunctor (ModuleCat R) i).obj X => a • x) := by
  let Y := (derivedComplexCompletionFunctor R a).obj X
  have hz (n : ℤ) (hn : n < 0) :
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) n).obj Y) :=
    (DerivedCategory.isGE_iff Y 0).mp hX n hn
  have hcone := unconditionalScalarCone_homology_isZero a Y (i - 1)
    (hz (i - 1) (by omega)) (hz (i - 1 + 1) (by omega))
  let η := (derivedComplexCompletionUnit R a).app X
  have hη := derivedScalarCone_map_isIso_of_completion R a η
    (derivedComplexCompletionFunctor_map_unit_isIso R a X) 1
  rw [pow_one] at hη
  have := hη
  let e := (DerivedCategory.homologyFunctor (ModuleCat R) (i - 1)).mapIso
    (asIso ((derivedScalarConeFunctor R a).map η))
  exact derived_homology_smul_injective_of_scalarCone_isZero a X i (hcone.of_iso e)

/-- 概要：完備化の負次数消滅と元の負次数の各元冪ねじれ性は、元の負次数を消す。
方針：前の単射性を反復し、冪で零になる各元を零へ戻す。
規約：ねじれ指数は元ごとに異なってよい。
使われ方：BS Rem 7.15（著者版 p.62）の raw 源の純性判定。 -/
theorem unconditional_isGE_of_completion_isGE_of_negative_power_torsion
    (X : ConcreteDerivedCategory R)
    (hX : ((derivedComplexCompletionFunctor R a).obj X).IsGE 0)
    (ht : ∀ i : ℤ, i < 0 →
      ∀ x : (DerivedCategory.homologyFunctor (ModuleCat R) i).obj X,
        ∃ n : ℕ, a ^ n • x = 0) : X.IsGE 0 := by
  apply (DerivedCategory.isGE_iff X 0).mpr
  intro i hi
  apply ModuleCat.isZero_iff_subsingleton.mpr
  apply subsingleton_of_forall_eq 0
  intro x
  obtain ⟨n, hn⟩ := ht i hi x
  have ha := unconditionalNegativeHomology_smul_injective_of_completion_isGE a X hX i hi
  have hzero (n : ℕ) (y : (DerivedCategory.homologyFunctor (ModuleCat R) i).obj X)
      (hy : a ^ n • y = 0) : y = 0 := by
    induction n with
    | zero => simpa using hy
    | succ n ih =>
      apply ih
      apply ha
      simpa only [pow_succ', mul_smul, smul_zero] using hy
  exact hzero n x hn

/-- 概要：主元局所化後に零になる加群の各元は、主元の冪で零になる。
方針：通常テンソルの局所化加群としての核判定を使う。
規約：ねじれ指数の一様性や有限生成性は不要。
使われ方：BS Rem 7.15（著者版 p.62）の局所化側のホモロジー消滅。 -/
theorem unconditionalModule_power_torsion_of_localization_isZero
    (B : Type u) [CommRing B] [Algebra R B] [IsLocalization.Away a B]
    (M : ModuleCat.{u} R)
    (h : IsZero ((ModuleCat.extendScalars (algebraMap R B)).obj M)) (x : M) :
    ∃ n : ℕ, a ^ n • x = 0 := by
  have hz : TensorProduct.mk R B M 1 x = 0 := by
    let e := extendScalarsObjEquivTensor R B M
    have := ModuleCat.isZero_iff_subsingleton.mp h
    have hs : Subsingleton (TensorProduct R B M) := e.symm.injective.subsingleton
    exact hs.elim _ _
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers a)
    (TensorProduct.mk R B M 1)).mp hz
  obtain ⟨n, hn⟩ := s.property
  exact ⟨n, by simpa only [Submonoid.smul_def, ← hn] using hs⟩

/-- 概要：実局所化の負次数消滅から、元の負次数の各元冪ねじれ性を得る。
方針：平坦な実導来係数拡大のホモロジー比較と、通常局所化の核判定を使う。
規約：任意の実導来対象に適用する。
使われ方：BS Rem 7.15（著者版 p.62）の局所化と完備化の合流。 -/
theorem unconditionalNegativeHomology_power_torsion_of_localization_isGE
    (B : Type u) [CommRing B] [Algebra R B] [IsLocalization.Away a B]
    (X : ConcreteDerivedCategory R)
    (h : ((flatDerivedBaseChange (algebraMap R B)
      (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat B (Submonoid.powers a)))).obj X).IsGE 0)
    (i : ℤ) (hi : i < 0)
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) i).obj X) :
    ∃ n : ℕ, a ^ n • x = 0 := by
  let hφ : (algebraMap R B).Flat :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat B (Submonoid.powers a))
  let e := (flatDerivedBaseChangeHomologyNatIso (algebraMap R B) hφ i).app X
  have hz := (DerivedCategory.isGE_iff _ 0).mp h i hi
  exact unconditionalModule_power_torsion_of_localization_isZero a B _ (hz.of_iso e.symm) x

/-- 概要：完備化と主元局所化が負次数を持たなければ、元の対象も負次数を持たない。
方針：局所化から各元冪ねじれ性、完備化から同じ主元の単射性を得る。
規約：元の実対象に関する結論であり、有界性・完備性・正則性を追加しない。
使われ方：BS Rem 7.15（著者版 p.62）の raw 源の純性判定。 -/
theorem unconditional_isGE_of_completion_isGE_of_localization_isGE
    (B : Type u) [CommRing B] [Algebra R B] [IsLocalization.Away a B]
    (X : ConcreteDerivedCategory R)
    (hc : ((derivedComplexCompletionFunctor R a).obj X).IsGE 0)
    (hl : ((flatDerivedBaseChange (algebraMap R B)
      (RingHom.flat_algebraMap_iff.mpr
        (IsLocalization.flat B (Submonoid.powers a)))).obj X).IsGE 0) :
    X.IsGE 0 :=
  unconditional_isGE_of_completion_isGE_of_negative_power_torsion a X hc
    (unconditionalNegativeHomology_power_torsion_of_localization_isGE a B X hl)

end SerrePositivity.BhattScholze.Andre
