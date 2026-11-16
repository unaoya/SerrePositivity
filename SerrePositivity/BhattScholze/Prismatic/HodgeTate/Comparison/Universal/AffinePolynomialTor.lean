module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineReducedPolynomialModel
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineFormsComplete
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineBasePolynomialAction

/-!
# 元の完備多項式係数加群の被覆へのTor消滅

## 概要
元の完備多項式係数加群は、指定被覆への係数拡大で高次Torを持たない。

## 方針
元の零番目の剰余行の完備自由多項式模型に、元の変数の包含と左逆を作る。

## 規約
元の基底作用への制限を使う。係数環全体の通常の平坦性は要求しない。

## 使われ方
元の完備形式のsingleと元のηの始域の被覆模型を計算する。
-/

public noncomputable section
universe u
open CategoryTheory AlgebraicTopology
open scoped Simplicial
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DerivedCompletion
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : IsBoundedPrism P) (r : ℕ)

include hP
/-- 元の完備多項式係数加群は、元の剰余行の実際の直和因子なので被覆への高次Torが消える。 -/
theorem affineRestrictedAlgebra_scalarExtensionTorVanishing :
    scalarExtensionTorVanishing (Construction61.crystallineCoverMap P).toRingHom
      ((ModuleCat.restrictScalars (affineBaseToPolynomialMap P r)).obj
        (ModuleCat.of (affineAlgebra P r) (affineAlgebra P r))) := by
  let k := A ⧸ P.ideal
  let S := AffineIndex.{u} r 0
  let C := MvPolynomial (S × ℕ) k
  let D := PrincipalCompletionH0 C (p : C)
  letI := principalCompletionCommRing C (p : C)
  let g : A →+* D := (principalCompletionUnitRingHom C (p : C)).comp
    (MvPolynomial.C.comp (Ideal.Quotient.mk P.ideal))
  letI := g.toAlgebra
  let R := affineAlgebra P r
  letI := Module.compHom R (affineBaseToPolynomialMap P r)
  let j : Fin r → S × ℕ := fun a => (ULift.up (a, 0), 0)
  let q : S × ℕ → Fin r := fun a => a.1.down.1
  let J := completedPolynomialRename.{u,0,u} k p j
  let Q := completedPolynomialRename.{u,u,0} k p q
  let JL : R →ₗ[A] D :=
    { __ := J.toAddMonoidHom
      map_smul' := fun a x => by
        change J (affineBaseToPolynomialMap P r a * x) = g a * J x
        rw [map_mul]
        congr 1
        exact completedPolynomialRename_C.{u,0,u} k p j (Ideal.Quotient.mk P.ideal a) }
  let QL : D →ₗ[A] R :=
    { __ := Q.toAddMonoidHom
      map_smul' := fun a x => by
        change Q (g a * x) = affineBaseToPolynomialMap P r a * Q x
        rw [map_mul]
        congr 1
        exact completedPolynomialRename_C.{u,u,0} k p q (Ideal.Quotient.mk P.ideal a) }
  letI : Module A ((reducedModel P hP r).obj ⦋0⦌) :=
    ModuleCat.isModule ((affineBaseModules P hP r).obj ⦋0⦌)
  obtain ⟨e⟩ := exists_affineReducedCompletedPolynomialLinearEquiv P hP r ⦋0⦌
  let M := (ModuleCat.restrictScalars (affineBaseToPolynomialMap P r)).obj
    (ModuleCat.of R R)
  let N := (affineBaseModules P hP r).obj ⦋0⦌
  let i : M ⟶ N := ModuleCat.ofHom (e.symm.toLinearMap.comp JL)
  let a : N ⟶ M := ModuleCat.ofHom (QL.comp e.toLinearMap)
  have hsplit : i ≫ a = 𝟙 M := by
    apply ModuleCat.hom_ext
    ext x
    change Q (e (e.symm (J x))) = x
    rw [LinearEquiv.apply_symm_apply]
    exact RingHom.congr_fun (completedPolynomialRename_split.{u,0,u} k p j q (fun _ => rfl)) x
  exact scalarExtensionTorVanishing_of_split (Construction61.crystallineCoverMap P).toRingHom
    i a hsplit (affineReducedCover_scalarExtensionTorVanishing P hP r ⦋0⦌)

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
