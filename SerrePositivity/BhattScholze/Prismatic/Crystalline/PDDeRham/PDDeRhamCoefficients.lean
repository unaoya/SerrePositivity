module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamBicomplex
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDRawPartialCoefficients
public import SerrePositivity.CommutativeAlgebra.DeRham.ExteriorCoefficientMap
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamColumn
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamRow
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDRawCoefficients
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor

/-!
# 完備 pd de Rham の係数変換

## 概要
完備した分冪係数と外冪を基底環の射に沿って写す。

## 方針
完備分冪係数を完備化の関手で写し、外冪の半線形写像とテンソルする。

## 規約
係数変換の前後で頂点の添字を固定する。

## 使われ方
整係数の Bockstein を mod p の総複体で比較する。
-/

public noncomputable section

open CategoryTheory SerrePositivity.DerivedCompletion SerrePositivity.DeRham
open scoped TensorProduct

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable (p : ℕ) (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] (r : ℕ)

private def rawCoeffRing (n : ℕ) : CommRingCat.of (pdRaw A r n) ⟶ CommRingCat.of (pdRaw B r n) :=
  CommRingCat.ofHom (pdRawCoefficients A B r n).toRingHom

private def pdTermCoefficientMap (n : ℕ) : pdTerm p A r n →ₛₗ[algebraMap A B] pdTerm p B r n :=
  let f := ringCatMap p (rawCoeffRing A B r n)
  { toFun := f.hom
    map_add' := f.hom.map_add
    map_smul' := fun a x => by
      change f.hom (a • x) = (algebraMap A B a) • f.hom x
      rw [Algebra.smul_def, Algebra.smul_def, map_mul]
      congr 1
      let jA := principalCompletionRingCatUnit p (CommRingCat.of (pdRaw A r n))
      let jB := principalCompletionRingCatUnit p (CommRingCat.of (pdRaw B r n))
      change f (jA (algebraMap A (pdRaw A r n) a)) =
        jB (algebraMap B (pdRaw B r n) (algebraMap A B a))
      exact (ConcreteCategory.congr_hom (ringCatMap_comp_unit p (rawCoeffRing A B r n)) _).trans
        (congrArg jB ((pdRawCoefficients A B r n).commutes a)) }

/-- 余単体の固定次数における完備 pd 形式の半線形な係数変換。 -/
def pdFormsCoefficientMap (n : SimplexCategory) (j : ℕ) :
    (pdRow p A r j).obj n →ₛₗ[algebraMap A B] (pdRow p B r j).obj n :=
  TensorProduct.map (pdTermCoefficientMap p A B r n.len)
    (exteriorPowerCoefficients A B (Fin r × Fin (n.len+1)) j)

private theorem pdTermCoefficientMap_unit (n : ℕ) (x : pdRaw A r n) :
    pdTermCoefficientMap p A B r n
      (principalCompletionRingCatUnit p (CommRingCat.of (pdRaw A r n)) x) =
    principalCompletionRingCatUnit p (CommRingCat.of (pdRaw B r n))
      (pdRawCoefficients A B r n x) :=
  ConcreteCategory.congr_hom (ringCatMap_comp_unit p (rawCoeffRing A B r n)) x

private theorem pdTermCoefficientMap_coface {m n : SimplexCategory} (θ : m ⟶ n)
    (x : pdTerm p A r m.len) :
    pdTermCoefficientMap p A B r n.len (pdTermMap p A r θ x) =
      pdTermMap p B r θ (pdTermCoefficientMap p A B r m.len x) := by
  have h : rawTermMap A r θ ≫ rawCoeffRing A B r n.len =
      rawCoeffRing A B r m.len ≫ rawTermMap B r θ :=
    (pdRawChange A B r).naturality θ
  have e := congrArg (principalCompletionRingFunctor p).map h
  rw [Functor.map_comp, Functor.map_comp] at e
  exact ConcreteCategory.congr_hom e x

set_option backward.isDefEq.respectTransparency false in
/-- 完備 pd 形式の係数変換は余単体の構造射と可換。 -/
theorem pdFormsCoefficientMap_natural {m n : SimplexCategory} (θ : m ⟶ n) (j : ℕ)
    (x : (pdRow p A r j).obj m) :
    pdFormsCoefficientMap p A B r n j ((pdRow p A r j).map θ x) =
      (pdRow p B r j).map θ (pdFormsCoefficientMap p A B r m j x) := by
  let f := pdFormsCoefficientMap p A B r
  suffices e : (f n j).comp ((pdRow p A r j).map θ).hom =
      ((pdRow p B r j).map θ).hom.comp (f m j) from DFunLike.congr_fun e x
  apply TensorProduct.ext'
  intro b w
  change (TensorProduct.map (pdTermCoefficientMap p A B r n.len)
      (exteriorPowerCoefficients A B (Fin r × Fin (n.len+1)) j))
    (TensorProduct.map (pdTermMap p A r θ) (exteriorPower.map j (copyModuleMap A r θ)) (b ⊗ₜ[A] w)) =
    (TensorProduct.map (pdTermMap p B r θ) (exteriorPower.map j (copyModuleMap B r θ)))
      (TensorProduct.map (pdTermCoefficientMap p A B r m.len)
        (exteriorPowerCoefficients A B (Fin r × Fin (m.len+1)) j) (b ⊗ₜ[A] w))
  simp only [TensorProduct.map_tmul, pdTermCoefficientMap_coface]
  congr 1
  exact exteriorPowerCoefficients_mapDomain A B (Fin r × Fin (m.len+1)) (copyIndex r θ) j w

set_option backward.isDefEq.respectTransparency false in
private theorem pdCompletedPartial_coefficients (n : ℕ) (a : pdCoordinates r n)
    (x : pdTerm p A r n) :
    pdTermCoefficientMap p A B r n (pdPartial p A r n a x) =
      pdPartial p B r n a (pdTermCoefficientMap p A B r n x) := by
  let : Module A (pdTerm p B r n) := Module.compHom _ (algebraMap A B)
  let : IsScalarTower A B (pdTerm p B r n) := IsScalarTower.of_compHom A B _
  let f : pdTerm p A r n →ₗ[A] pdTerm p B r n :=
    { toFun := pdTermCoefficientMap p A B r n
      map_add' := map_add _
      map_smul' a x := (pdTermCoefficientMap p A B r n).map_smulₛₗ a x }
  let l := f.comp (pdPartial p A r n a)
  let m := ((pdPartial p B r n a).restrictScalars A).comp f
  have hm : IsModuleComplete A (p : A) (ModuleCat.of A (pdTerm p B r n)) :=
    (isModuleComplete_algebraMap_iff A B (p : A) (pdTerm p B r n)).mp (by
      rw [map_natCast]
      exact completedRing_isModuleComplete B p)
  have h : l = m := by
    apply principalCompletionLinearMap_ext A p hm
    intro y
    let uA := principalCompletionRingCatUnit p (CommRingCat.of (pdRaw A r n))
    let uB := principalCompletionRingCatUnit p (CommRingCat.of (pdRaw B r n))
    change pdTermCoefficientMap p A B r n (pdPartial p A r n a (uA y)) =
      pdPartial p B r n a (pdTermCoefficientMap p A B r n (uA y))
    have hA := principalCompletionLinearMap_unit A p (A := pdRaw A r n) (B := pdRaw A r n)
      (pdRawPartial A r n a) y
    have hB := principalCompletionLinearMap_unit B p (A := pdRaw B r n) (B := pdRaw B r n)
      (pdRawPartial B r n a)
      (pdRawCoefficients A B r n y)
    change pdPartial p A r n a (uA y) = uA (pdRawPartial A r n a y) at hA
    change pdPartial p B r n a (uB (pdRawCoefficients A B r n y)) =
      uB (pdRawPartial B r n a (pdRawCoefficients A B r n y)) at hB
    rw [hA, pdTermCoefficientMap_unit, pdTermCoefficientMap_unit, hB,
      pdRawPartial_coefficients]
  exact DFunLike.congr_fun h x

private theorem pdCoordinateOne_coefficients (n : SimplexCategory) (a : pdCoordinates r n.len) :
    exteriorPowerCoefficients A B (Fin r × Fin (n.len+1)) 1 (pdCoordinateOne A r n a) =
      pdCoordinateOne B r n a := by
  rw [pdCoordinateOne, pdCoordinateOne, exteriorPowerCoefficients_one]
  congr 1
  rcases a with t | ⟨t,i⟩
  · exact freeCoefficientMap_single A B _ (t,0)
  · change freeCoefficientMap A B _ (Finsupp.single (t,i.succ) 1 - Finsupp.single (t,0) 1) = _
    rw [map_sub, freeCoefficientMap_single, freeCoefficientMap_single]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- 完備 pd 形式の係数変換は列の微分と可換。 -/
theorem pdFormsCoefficientMap_d (n : SimplexCategory) (j : ℕ) (x : (pdRow p A r j).obj n) :
    pdFormsCoefficientMap p A B r n (j+1) (pdVerticalD p A r n j x) =
      pdVerticalD p B r n j (pdFormsCoefficientMap p A B r n j x) := by
  let f := pdFormsCoefficientMap p A B r n
  suffices e : (f (j+1)).comp (pdVerticalD p A r n j).hom =
      (pdVerticalD p B r n j).hom.comp (f j) from DFunLike.congr_fun e x
  apply TensorProduct.ext'
  intro b w
  change pdTerm p A r n.len at b
  change ⋀[A]^j (CopyModule A r n) at w
  change f (j+1) ((∑ a : pdCoordinates r n.len, TensorProduct.map (pdPartial p A r n.len a)
    (wedgeOne A (CopyModule A r n) j (pdCoordinateOne A r n a))) (b ⊗ₜ[A] w)) =
    (∑ a : pdCoordinates r n.len, TensorProduct.map (pdPartial p B r n.len a)
      (wedgeOne B (CopyModule B r n) j (pdCoordinateOne B r n a))) (f j (b ⊗ₜ[A] w))
  simp only [LinearMap.sum_apply, TensorProduct.map_tmul, map_sum, f, pdFormsCoefficientMap]
  apply Finset.sum_congr rfl
  intro a _
  let e (l : ℕ) := exteriorPowerCoefficients A B (Fin r × Fin (n.len+1)) l
  let c := pdTermCoefficientMap p A B r n.len
  let dA := pdPartial p A r n.len a
  let dB := pdPartial p B r n.len a
  let wA := wedgeOne A (CopyModule A r n) j (pdCoordinateOne A r n a)
  let wB := wedgeOne B (CopyModule B r n) j (pdCoordinateOne B r n a)
  change TensorProduct.map c (e (j+1)) (dA b ⊗ₜ[A] wA w) =
    TensorProduct.map dB wB (TensorProduct.map c (e j) (b ⊗ₜ[A] w))
  rw [TensorProduct.map_tmul, TensorProduct.map_tmul, TensorProduct.map_tmul,
    pdCompletedPartial_coefficients]
  congr 1
  dsimp only [e, wA, wB]
  rw [exteriorPowerCoefficients_wedgeOne, pdCoordinateOne_coefficients]

end SerrePositivity.BhattScholze.Prismatic
