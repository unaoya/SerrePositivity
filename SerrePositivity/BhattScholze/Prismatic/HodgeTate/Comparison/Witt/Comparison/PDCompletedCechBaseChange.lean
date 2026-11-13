module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.CompletedCechCoefficientMap
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDCompletedCoefficientComplex
import all Mathlib.Algebra.Category.CommAlgCat.Basic
import all Mathlib.Algebra.Category.ModuleCat.Basic
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.Algebra
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.CompletedCechCoefficientMap
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDCompletedCoefficientComplex
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDTermPointwiseNaturality
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDTermCompletedTensor
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCompletedCech
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamCech
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.MapComplex
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.PointwiseBaseChange

/-!
# 小さい分冪 Čech 係数射の完備延長

## 概要
小さい分冪模型の係数変更の標準完備延長は、交代余面複体で同型になる。

## 方針
純テンソルの単位上で、既存の各項の完備テンソル比較同型に一致することを示す。

## 規約
各項の H⁰ 完備係数拡大の射。導来底変換を計算するための正則性・完全平坦性とは分けて述べる。

## 使われ方
BS 著者版 Theorem 6.4、Witt から剰余係数への比較を有限枠で検査する。
-/

public noncomputable section
open CategoryTheory AlgebraicTopology
open scoped Simplicial TensorProduct ChangeOfRings
open SerrePositivity.DerivedCompletion
universe u
namespace SerrePositivity.BhattScholze.Prismatic
set_option backward.isDefEq.respectTransparency false
variable (p : ℕ) (k l : Type u) [CommRing k] [CommRing l] [Algebra k l] (r : ℕ)

private theorem modelComplete (n : SimplexCategory) :
    IsModuleComplete l (p : l) ((pdModel p l r ⋙ PDCechNerve.algebraModule l).obj n) := by
  change IsModuleComplete l (p : l) (ModuleCat.of l (pdTerm p l r n.len))
  exact completedRing_isModuleComplete l p (A := pdRaw l r n.len)

/-- 小さい分冪模型の係数変更を標準の完備 Čech 係数射として読む。 -/
def pdCompletedCechBaseChange :
    ((pCompletedScalarExtensionFunctor p (algebraMap k l)).mapHomologicalComplex _).obj
      ((alternatingCofaceMapComplex (ModuleCat.{u} k)).obj
        (pdModel p k r ⋙ PDCechNerve.algebraModule k)) ⟶
    (alternatingCofaceMapComplex (ModuleCat.{u} l)).obj
      (pdModel p l r ⋙ PDCechNerve.algebraModule l) :=
  completedUnderCechCoefficientCochainMap p k l (pdModel p k r) (pdModel p l r)
    (pdModelBaseChange p k l r) (modelComplete p l r)

/-- 係数変更の標準完備延長は、各項の完備テンソル比較から作った同型の射である。 -/
private theorem pdCompletedCechBaseChange_eq :
    pdCompletedCechBaseChange p k l r = (pdCompletedCoefficientComplexIso p k l r).hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply pCompletedScalarExtension_hom_ext p k l (pdTerm p k r n)
    (ModuleCat.of l (pdTerm p l r n)) (completedRing_isModuleComplete l p (A := pdRaw l r n))
  intro b x
  have hl := completedUnderCechCoefficientMap_unit p k l (pdModel p k r) (pdModel p l r)
    (pdModelBaseChange p k l r) (modelComplete p l r) ⦋n⦌ b x
  have hr := pdTermPointwiseCoefficientIso_unit_smul p k l r n b x
  exact hl.trans hr.symm

/-- 小さい分冪模型の標準完備係数射は交代余面複体の同型。 -/
theorem pdCompletedCechBaseChange_isIso : IsIso (pdCompletedCechBaseChange p k l r) := by
  rw [pdCompletedCechBaseChange_eq]
  infer_instance

/-- 小さい分冪模型の標準完備係数射は擬同型。 -/
theorem pdCompletedCechBaseChange_quasiIso : QuasiIso (pdCompletedCechBaseChange p k l r) := by
  let := pdCompletedCechBaseChange_isIso p k l r
  infer_instance

end SerrePositivity.BhattScholze.Prismatic
