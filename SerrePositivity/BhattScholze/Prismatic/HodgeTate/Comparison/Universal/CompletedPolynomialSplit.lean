module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.TorAcyclicRetracts
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.Comparisons
public import Mathlib.Algebra.MvPolynomial.Rename

/-!
# 元の主完備多項式環の変数に沿う実際の分裂

## 概要
変数の包含とその左逆から、元のp完備多項式環の分裂する二本の射を作る。

## 方針
元のrenameを元の主完備化の普遍性で延長し、標準単位の上で合成を照合する。

## 規約
完備化を抽象的に置き換えない。基底係数も元の標準単位で保つ。

## 使われ方
元の完備形式を、検証済みの元の完備自由多項式行の直和因子へ戻す。
-/

public noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DerivedCompletion
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (k : Type u) [CommRing k] {T S : Type u} (p : ℕ)

/-- 元の主完備多項式環の、元の変数変更による射。 -/
def completedPolynomialRename (j : T → S) :
    letI := principalCompletionCommRing (MvPolynomial T k) (p : MvPolynomial T k)
    letI := principalCompletionCommRing (MvPolynomial S k) (p : MvPolynomial S k)
    PrincipalCompletionH0 (MvPolynomial T k) (p : MvPolynomial T k) →+*
      PrincipalCompletionH0 (MvPolynomial S k) (p : MvPolynomial S k) :=
  principalCompletionMap (MvPolynomial.rename j).toRingHom
    (p : MvPolynomial T k) (p : MvPolynomial S k) (map_natCast _ p)

/-- 同じ変数変更は元の多項式の完備化単位を保つ。 -/
theorem completedPolynomialRename_unit (j : T → S) (x : MvPolynomial T k) :
    letI := principalCompletionCommRing (MvPolynomial T k) (p : MvPolynomial T k)
    letI := principalCompletionCommRing (MvPolynomial S k) (p : MvPolynomial S k)
    completedPolynomialRename k p j
      (principalCompletionUnitRingHom (MvPolynomial T k) (p : MvPolynomial T k) x) =
      principalCompletionUnitRingHom (MvPolynomial S k) (p : MvPolynomial S k)
        (MvPolynomial.rename j x) :=
  by
    letI := principalCompletionCommRing (MvPolynomial T k) (p : MvPolynomial T k)
    letI := principalCompletionCommRing (MvPolynomial S k) (p : MvPolynomial S k)
    let φ : MvPolynomial T k →+* MvPolynomial S k := (MvPolynomial.rename j).toRingHom
    change principalCompletionMap φ (p : MvPolynomial T k) (p : MvPolynomial S k)
        (map_natCast φ p)
        (principalCompletionUnitRingHom (MvPolynomial T k) (p : MvPolynomial T k) x) =
      principalCompletionUnitRingHom (MvPolynomial S k) (p : MvPolynomial S k) (φ x)
    have h := principalCompletionMap_comp φ (p : MvPolynomial T k) (p : MvPolynomial S k)
      (map_natCast φ p)
    exact RingHom.congr_fun h x

/-- 元の多項式変数の分裂は、同じ二本の完備化された射で分裂する。 -/
theorem completedPolynomialRename_split (j : T → S) (q : S → T) (h : Function.LeftInverse q j) :
    letI := principalCompletionCommRing (MvPolynomial T k) (p : MvPolynomial T k)
    letI := principalCompletionCommRing (MvPolynomial S k) (p : MvPolynomial S k)
    (completedPolynomialRename k p q).comp (completedPolynomialRename k p j) = RingHom.id _ := by
  letI := principalCompletionCommRing (MvPolynomial T k) (p : MvPolynomial T k)
  letI := principalCompletionCommRing (MvPolynomial S k) (p : MvPolynomial S k)
  have hcomp : ((completedPolynomialRename k p q).comp (completedPolynomialRename k p j)).comp
      (principalCompletionUnitRingHom (MvPolynomial T k) (p : MvPolynomial T k)) =
      principalCompletionUnitRingHom (MvPolynomial T k) (p : MvPolynomial T k) := by
    apply RingHom.ext
    intro x
    change completedPolynomialRename k p q (completedPolynomialRename k p j
      (principalCompletionUnitRingHom (MvPolynomial T k) (p : MvPolynomial T k) x)) = _
    rw [completedPolynomialRename_unit, completedPolynomialRename_unit, MvPolynomial.rename_rename]
    have hj : q ∘ j = id := funext h
    rw [hj, MvPolynomial.rename_id_apply]
  exact (principalCompletion_existsUnique_ringHom (MvPolynomial T k) (p : MvPolynomial T k) _
    (principalCompletionUnitRingHom (MvPolynomial T k) (p : MvPolynomial T k))
    (principalCompletion_isModuleComplete_unit (p : MvPolynomial T k))).unique
      hcomp (RingHom.id_comp _)

/-- 同じ係数の定数多項式の像は、元の完備化単位のまま。 -/
theorem completedPolynomialRename_C (j : T → S) (a : k) :
    completedPolynomialRename k p j
      (principalCompletionUnitRingHom (MvPolynomial T k) (p : MvPolynomial T k) (MvPolynomial.C a)) =
      principalCompletionUnitRingHom (MvPolynomial S k) (p : MvPolynomial S k) (MvPolynomial.C a) := by
  rw [completedPolynomialRename_unit, MvPolynomial.rename_C]

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
