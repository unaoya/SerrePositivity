module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineFormsProjective
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffinePolynomialCoefficients

/-!
# 元の完備形式の基底を保つ向き付き係数射

## 概要
元の有限自由な完備形式の外積基底を保つ半線形係数射を固定する。

## 方針
元のaffine係数環の射を通じた作用で基底から線形延長する。

## 規約
コホモロジーの同型性や係数拡大の平坦性は仮定しない。

## 使われ方
HT04.R2の同じ零次・一次形式と標準HT写像の照合。
-/

public noncomputable section
universe u
open CategoryTheory SerrePositivity.DeRham
open scoped TensorProduct
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable {P : OrientedPrism p A} {Q : OrientedPrism p B}
/-- 元の完備形式の、完備化単位を保つ外積座標の基底。 -/
def affineFormsCoordinateBasis (P : OrientedPrism p A) (r i : ℕ) :
    Module.Basis (Set.powersetCard (formVars.{u} r) i) (affineAlgebra P r) (affineForms P r i) := by
  let k := A ⧸ P.ideal
  let T := formVars.{u} r
  let B := Poly k T
  let C := completedPoly k T p
  letI := completedPoly_isScalarTower k T p
  let E := ⋀[k]^i (T → k)
  let e : affineForms P r i ≃ₗ[C] C ⊗[k] E :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange k B C C E
  let b := (((Pi.basisFun k T).exteriorPower i).baseChange C).map e.symm
  exact b.mapCoeffs (affineCoordinateIso P r).symm (fun q w => by
    change affineCoordinateIso P r ((affineCoordinateIso P r).symm q) • w = q • w
    rw [RingEquiv.apply_symm_apply])

variable (f : OrientedPrism.Hom P Q) (r i : ℕ)

/-- 元の外積基底を保つ、元の完備係数環の射に関する半線形写像。 -/
def affineFormsCoefficientAny :
    affineForms P r i →ₛₗ[affinePolynomialCoefficientMap f r] affineForms Q r i := by
  letI := Module.compHom (affineForms Q r i) (affinePolynomialCoefficientMap f r)
  let g : affineForms P r i →ₗ[affineAlgebra P r] affineForms Q r i :=
    (affineFormsCoordinateBasis P r i).constr ℤ
    (fun t => affineFormsCoordinateBasis Q r i t)
  exact
    { __ := g.toAddMonoidHom
      map_smul' := fun a x => g.map_smul a x }

/-- この係数射は、元の完備外積基底の各ベクトルを同じ基底ベクトルへ送る。 -/
theorem affineFormsCoefficientAny_basis (t : Set.powersetCard (formVars.{u} r) i) :
    affineFormsCoefficientAny f r i (affineFormsCoordinateBasis P r i t) =
      affineFormsCoordinateBasis Q r i t := by
  letI := Module.compHom (affineForms Q r i) (affinePolynomialCoefficientMap f r)
  exact Module.Basis.constr_basis (affineFormsCoordinateBasis P r i) ℤ _ t

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
