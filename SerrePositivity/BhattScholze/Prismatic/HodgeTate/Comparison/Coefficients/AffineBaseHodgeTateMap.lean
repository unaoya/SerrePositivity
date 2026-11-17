module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineBasePolynomialAction
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.AffineCrystallineBaseCohomology
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.AffineCochainMap

/-!
# 元の基底環上で読む標準 Hodge–Tate 写像

## 概要
元の完備多項式線形な HT 写像を、同じ基底環上の複体のホモロジーへ移す。

## 方針
元の作用の制限の自然同型と、スカラー制限の標準ホモロジー同型を使う。

## 規約
HT 写像を選び直さない。基底環上の形式の作用も同じ多項式作用の制限から取る。

## 使われ方
特定の Zp 係数射の平坦なホモロジー係数変更へ、既存の標準 HT 写像を渡す。
-/

public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
open HTComparisonTotal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : IsBoundedPrism P) (r : ℕ)

/-- 元の多項式係数複体の制限と、元の基底係数複体の自然な同型。 -/
def affineBasePolynomialComplexIso :
    ((ModuleCat.restrictScalars (affineBaseToPolynomialMap P r)).mapHomologicalComplex (.up ℕ)).obj
        (affineHTComplex P hP r) ≅ affineBaseComplex P hP r :=
  (alternatingCofaceFunctorIso (ModuleCat.restrictScalars
      (affineBaseToPolynomialMap P r))).app (affineHTModules P hP r) ≪≫
    (alternatingCofaceMapComplex (ModuleCat.{u} A)).mapIso
      (affineBaseModulesPolynomialIso P hP r).symm

/-- 同じ係数作用の制限による、元のホモロジーへの指定同型。 -/
def affineBasePolynomialCohomologyIso (i : ℕ) :
    (ModuleCat.restrictScalars (affineBaseToPolynomialMap P r)).obj
        ((affineHTComplex P hP r).homology i) ≅ (affineBaseComplex P hP r).homology i :=
  (((affineHTComplex P hP r).sc i).mapHomologyIso
      (ModuleCat.restrictScalars (affineBaseToPolynomialMap P r))).symm ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (.up ℕ) i).mapIso
      (affineBasePolynomialComplexIso P hP r)

/-- 同じ標準 HT 写像を、元の基底作用に関する線形写像として読む。 -/
def affineBaseHTMap (i : ℕ) :
    letI := Module.compHom (affineForms P r i) (affineBaseToPolynomialMap P r)
    affineForms P r i →ₗ[A] (affineBaseComplex P hP r).homology i := by
  letI := Module.compHom (affineForms P r i) (affineBaseToPolynomialMap P r)
  let F := ModuleCat.restrictScalars (affineBaseToPolynomialMap P r)
  let L : affineForms P r i →ₗ[A] F.obj ((affineHTComplex P hP r).homology i) :=
    { __ := (affineHTMap P hP r i).toAddHom
      map_smul' := fun a x => by
        change affineHTMap P hP r i (affineBaseToPolynomialMap P r a • x) =
          affineBaseToPolynomialMap P r a • affineHTMap P hP r i x
        exact (affineHTMap P hP r i).map_smul _ _ }
  exact (affineBasePolynomialCohomologyIso P hP r i).hom.hom.comp L

/-- 元の基底作用での全単射性と、元の標準 HT 写像での全単射性は同値。 -/
theorem affineBaseHTMap_bijective_iff (i : ℕ) :
    Function.Bijective (affineBaseHTMap P hP r i) ↔ Function.Bijective (affineHTMap P hP r i) := by
  let E := (affineBasePolynomialCohomologyIso P hP r i).toLinearEquiv
  change Function.Bijective (fun x => E (affineHTMap P hP r i x)) ↔ _
  constructor
  · rintro ⟨hinj, hsurj⟩
    constructor
    · intro x y h
      exact hinj (congrArg E h)
    · intro y
      obtain ⟨x, hx⟩ := hsurj (E y)
      exact ⟨x, E.injective hx⟩
  · intro h
    exact E.bijective.comp h

/-- 目標の元の古典的な型は、同じ基底複体の標準写像で判定できる。 -/
theorem hodgeTateIsoStatement_iff_affineBaseHTMap_bijective :
    HodgeTateIsoStatement P hP r ↔ ∀ i, Function.Bijective (affineBaseHTMap P hP r i) := by
  rw [hodgeTateIsoStatement_iff_affineHTMap_bijective]
  exact forall_congr' (fun i => (affineBaseHTMap_bijective_iff P hP r i).symm)

end SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
