module


public meta import SerrePositivity.Util.Citation
public import Mathlib.RingTheory.Localization.Integral
public import SerrePositivity.BhattScholze.Almost.IntegralClosureCompletion
public import SerrePositivity.CommutativeAlgebra.IntegralApproximation.FilteredAlgebra

/-!
# 整閉包の局所化を固定した有限近似

## 概要
BS 著者版 Theorem 10.11 の証明で、Lemma 10.12 の層の整閉包を有限表示有限代数で近似する。

## 方針
有限エタールな局所化の各元を、分母を払って整閉包に入れる。局所化を固定できる有限近似を適用する。

## 規約
各近似から整閉包への射と、主局所化から層への指定射を保持する。

## 使われ方
Theorem 10.9 を各近似に適用し、Theorem 10.11 の組み立てに渡す。
-/

@[expose] public noncomputable section

universe u
open _root_.CategoryTheory _root_.CategoryTheory.Limits

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

open _root_.SerrePositivity.BhattScholze.PerfectoidizationInterface

attribute [local instance] _root_.SerrePositivity.BhattScholze.Almost.reducedAwayBase

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

private theorem _root_.SerrePositivity.BhattScholze.Almost.reducedAway_algebraMap_isUnit (g : R) :
    IsUnit (algebraMap R (_root_.SerrePositivity.BhattScholze.Almost.reducedAway R S g) g) :=
  IsLocalization.Away.algebraMap_isUnit (algebraMap R (S ⧸ nilradical S) g)

/-- Theorem 10.11 の g-almost 部分に使う。近似の主局所化は指定した有限エタール層に一致する。 -/
theorem _root_.SerrePositivity.BhattScholze.Almost.exists_finitePresentation_approximation_fixedLocalization (g : R)
    (het : _root_.SerrePositivity.BhattScholze.Almost.FiniteEtaleAway R (S ⧸ nilradical S) g) :
    let T := _root_.SerrePositivity.BhattScholze.Almost.integralClosureInLocalization R S g
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsFiltered I) (F : I ⥤ A_R R)
      (η : F ⟶ (Functor.const I).obj (ofAlgebra R T)),
      Nonempty (IsColimit (Cocone.mk _ η)) ∧ ∀ i, _root_.SerrePositivity.CommutativeAlgebra.FinitePresentedFinite R (F.obj i) ∧
        let a := (F.obj i).hom.hom g
        let f := T.val.toRingHom.comp (η.app i).right.hom
        Function.Bijective (IsLocalization.Away.lift (S := Localization.Away a) a (g := f)
          (by
            have he := congrArg (fun k : CommRingCat.of R ⟶ CommRingCat.of T => k.hom g)
              (Under.w (η.app i))
            change (η.app i).right.hom a = algebraMap R T g at he
            change IsUnit (T.val ((η.app i).right.hom a))
            rw [he, T.val.commutes]
            exact _root_.SerrePositivity.BhattScholze.Almost.reducedAway_algebraMap_isUnit R S g)) := by
  let T := _root_.SerrePositivity.BhattScholze.Almost.integralClosureInLocalization R S g
  let B := _root_.SerrePositivity.BhattScholze.Almost.reducedAway R S g
  let L := Localization.Away g
  let a₁ : Algebra R L := inferInstanceAs (Algebra R (Localization.Away g))
  let a₂ : Algebra L B := _root_.SerrePositivity.GenericEtale.awayAlgebra R (S ⧸ nilradical S) g
  let : Algebra R L := a₁
  let : Algebra L B := a₂
  let : Algebra R B := _root_.SerrePositivity.BhattScholze.Almost.reducedAwayBase R S g
  let : SMul R L := a₁.toSMul
  let : SMul L B := a₂.toSMul
  let : SMul R B := (_root_.SerrePositivity.BhattScholze.Almost.reducedAwayBase R S g).toSMul
  let : IsScalarTower R L B := IsScalarTower.of_algebraMap_eq fun r => by
    change (algebraMap (S ⧸ nilradical S) B) (algebraMap R (S ⧸ nilradical S) r) =
      Localization.awayMap (algebraMap R (S ⧸ nilradical S)) g (algebraMap R L r)
    exact (IsLocalization.map_eq (M := Submonoid.powers g) (S := Localization.Away g)
      (T := Submonoid.powers (algebraMap R (S ⧸ nilradical S) g))
      (Q := _root_.SerrePositivity.BhattScholze.Almost.reducedAway R S g) (g := algebraMap R (S ⧸ nilradical S))
      (hy := by
        rintro _ ⟨n, rfl⟩
        exact ⟨n, (map_pow (algebraMap R (S ⧸ nilradical S)) g n).symm⟩) r).symm
  let : Module.Finite L B := het.1
  let : Algebra.Etale L B := het.2
  let : Algebra.FinitePresentation R L := IsLocalization.Away.finitePresentation g
  let : Algebra.FinitePresentation R B := Algebra.FinitePresentation.trans R L B
  have hT : Algebra.IsIntegral R T := T.isIntegral_iff.mpr fun _ h => h
  apply _root_.SerrePositivity.CommutativeAlgebra.integral_isFilteredColimit_finitePresentation_fixedLocalization hT g T.val
    (_root_.SerrePositivity.BhattScholze.Almost.reducedAway_algebraMap_isUnit R S g) Subtype.val_injective
  intro x
  obtain ⟨⟨m, n, rfl⟩, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
    (Submonoid.powers g) (Rₘ := L) x (IsIntegral.of_finite L x)
  have he : (g ^ n) • x = (algebraMap R B g) ^ n * x := by
    rw [Algebra.smul_def, map_pow]
  refine ⟨n, ⟨(g ^ n) • x, hm⟩, he⟩

end SerrePositivity.BhattScholze.Perfectoidization.Derived

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Thm 10.11" (partial := component) "filtered 余極限への帰着、有限表示近似、perfectoid の余極限の完備化（BS-W13）。離散性の本体は A6・A7 待ち。E3 の欄は引き続き Inputs ／ 11-10 更新"] _root_.SerrePositivity.BhattScholze.Almost.exists_finitePresentation_approximation_fixedLocalization
