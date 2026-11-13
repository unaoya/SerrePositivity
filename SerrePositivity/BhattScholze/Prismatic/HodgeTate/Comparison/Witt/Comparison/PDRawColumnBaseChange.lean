module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDRawColumnCompletion
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.PDDeRham.PDRawFormsBaseChange
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDRawPartialCoefficients
public import SerrePositivity.HomologicalAlgebra.BaseChange
public import SerrePositivity.HomologicalAlgebra.AlgebraScalarExtensionModule
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDRawColumnCompletion
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.PDDeRham.PDRawFormsBaseChange
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDRawDeRhamColumn
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamCoefficients
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamRow
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamColumn

/-!
# 未完備分冪 de Rham 列の底変換

## 概要
自由模型の各項の底変換を微分と照合し、列全体の底変換同型を作る。

## 方針
分冪偏微分と外冪の係数変更の公式を純テンソルで適用する。

## 規約
基底環の射には平坦性を仮定しない。

## 使われ方
BS 著者版 Theorem 6.4 の完備導来底変換に使う自由模型の比較。
-/

public noncomputable section

open CategoryTheory SerrePositivity.DeRham
open scoped TensorProduct Simplicial ChangeOfRings

universe u

namespace SerrePositivity.BhattScholze.Prismatic

set_option backward.isDefEq.respectTransparency false

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] (r : ℕ) (n : SimplexCategory)

private theorem pdRawFormsCoefficientMap_d (j : ℕ) (x : pdRawForms A r n j) :
    pdRawFormsCoefficientMap A B r n.len (j + 1) (pdRawVertical A r n j x) =
      pdRawVertical B r n j (pdRawFormsCoefficientMap A B r n.len j x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a w =>
    change pdRaw A r n.len at a
    change ⋀[A]^j (CopyModule A r n) at w
    simp only [pdRawVertical, LinearMap.sum_apply, TensorProduct.map_tmul,
      map_sum, pdRawFormsCoefficientMap]
    apply Finset.sum_congr rfl
    intro t _
    change pdRawCoefficients A B r n.len (pdRawPartial A r n.len t a) ⊗ₜ[B]
      exteriorPowerCoefficients A B _ (j + 1)
        (wedgeOne A _ j (pdCoordinateOne A r n t) w) =
      pdRawPartial B r n.len t (pdRawCoefficients A B r n.len a) ⊗ₜ[B]
        wedgeOne B _ j (pdCoordinateOne B r n t) (exteriorPowerCoefficients A B _ j w)
    rw [pdRawPartial_coefficients, exteriorPowerCoefficients_wedgeOne, pdCoordinateOne_coefficients]

/-- 未完備分冪列の係数変更を係数制限した余鎖写像として読む。 -/
def pdUncompletedColumnCoefficientHom :
    pdUncompletedColumn A r n ⟶
      ((ModuleCat.restrictScalars (algebraMap A B)).mapHomologicalComplex (.up ℕ)).obj
        (pdUncompletedColumn B r n) :=
  CochainComplex.ofHom (fun j =>
    ModuleCat.semilinearMapAddEquiv (algebraMap A B) _ _
      (pdRawFormsCoefficientMap A B r n.len j)) (by
      intro j
      change _ ≫ (ModuleCat.restrictScalars (algebraMap A B)).map
        ((pdUncompletedColumn B r n).d j (j + 1)) =
        (pdUncompletedColumn A r n).d j (j + 1) ≫ _
      dsimp only [pdUncompletedColumn]
      rw [CochainComplex.of_d, CochainComplex.of_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact (pdRawFormsCoefficientMap_d A B r n j x).symm)

private def termBaseChangeEquiv (j : ℕ) :
    ((ModuleCat.extendScalars (algebraMap A B)).obj
      ((pdUncompletedColumn A r n).X j)) ≅ (pdUncompletedColumn B r n).X j :=
  algebraScalarExtensionModuleIso A B ((pdUncompletedColumn A r n).X j) ≪≫
    (pdRawFormsCoefficientMap_isBaseChange A B r n.len j).equiv.toModuleIso

private theorem termBaseChange_tmul (j : ℕ) (b : B) (x : (pdUncompletedColumn A r n).X j) :
    (termBaseChangeEquiv A B r n j).hom (b ⊗ₜ[A,algebraMap A B] x) =
      b • pdRawFormsCoefficientMap A B r n.len j x := by
  simp only [termBaseChangeEquiv, Iso.trans_hom, ConcreteCategory.comp_apply]
  exact (pdRawFormsCoefficientMap_isBaseChange A B r n.len j).equiv_tmul b x

/-- 自由模型の列は通常の底変換と可換。 -/
def pdUncompletedColumnBaseChangeIso :
    ((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex (.up ℕ)).obj
        (pdUncompletedColumn A r n) ≅ pdUncompletedColumn B r n :=
  HomologicalComplex.Hom.isoOfComponents (termBaseChangeEquiv A B r n) (by
    intro i j hij
    obtain rfl : i + 1 = j := hij
    apply (ModuleCat.ExtendRestrictScalarsAdj.homEquiv (algebraMap A B)).injective
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (pdUncompletedColumn B r n).d i (i + 1)
      ((termBaseChangeEquiv A B r n i).hom ((1 : B) ⊗ₜ[A,algebraMap A B] x)) =
      (termBaseChangeEquiv A B r n (i + 1)).hom
        ((ModuleCat.extendScalars (algebraMap A B)).map
          ((pdUncompletedColumn A r n).d i (i + 1)) ((1 : B) ⊗ₜ[A,algebraMap A B] x))
    rw [termBaseChange_tmul, ModuleCat.ExtendScalars.map_tmul, termBaseChange_tmul,
      one_smul, one_smul]
    have hD (C : Type u) [CommRing C] :
        (pdUncompletedColumn C r n).d i (i + 1) = ModuleCat.ofHom (pdRawVertical C r n i) := by
      dsimp only [pdUncompletedColumn]
      exact CochainComplex.of_d _ _ i
    rw [hD A, hD B]
    change pdRawVertical B r n i (pdRawFormsCoefficientMap A B r n.len i x) =
      pdRawFormsCoefficientMap A B r n.len (i + 1) (pdRawVertical A r n i x)
    exact (pdRawFormsCoefficientMap_d A B r n i x).symm)


end SerrePositivity.BhattScholze.Prismatic
