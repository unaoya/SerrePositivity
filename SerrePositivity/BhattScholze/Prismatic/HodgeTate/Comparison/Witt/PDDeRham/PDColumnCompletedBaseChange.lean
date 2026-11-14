module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.PDDeRham.PDColumnCompletionEquivalence
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDRawColumnBaseChange
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDRawColumnBoundedModel
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedBaseChangeModel
public import SerrePositivity.HomologicalAlgebra.MapExtend
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDRawColumnBoundedModel
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDRawColumnCompletion

/-!
# 第 0 分冪 de Rham 列の完備導来底変換

## 概要
p 正則な基底環の射について、完備第 0 列の完備導来底変換を標的の完備第 0 列で計算する。

## 方針
もとの自由な有界列を射影模型に使い、未完備列の底変換同型と完備化同値を合成する。

## 規約
環射の平坦性は仮定しない。実際の係数変更は自由模型からの標準射で指定する。

## 使われ方
BS 著者版 Theorem 6.4 の W(C) から C への比較。
-/

public noncomputable section

open CategoryTheory SerrePositivity.DerivedCompletion
open scoped Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic

set_option backward.isDefEq.respectTransparency false
attribute [local instance] HasDerivedCategory.standard

variable (p : ℕ) (k : Type u) [CommRing k] (r : ℕ)

local notation "emb" => ComplexShape.embeddingUpNat

/-- 未完備第 0 列を上に有界な導来対象として読む。 -/
def pdUncompletedColumnZeroDerived : DerivedCategory.Minus (ModuleCat.{u} k) :=
  ⟨DerivedCategory.Q.obj ((pdUncompletedColumn k r ⦋0⦌).extend emb), ⟨r, by
    have := pdUncompletedColumnZero_isStrictlyLE k r
    infer_instance⟩⟩

/-- 完備第 0 列を上に有界な導来対象として読む。 -/
def pdCompletedColumnZeroDerived : DerivedCategory.Minus (ModuleCat.{u} k) :=
  ⟨DerivedCategory.Q.obj ((pdDeRhamColumn p k r ⦋0⦌).extend emb), ⟨r, by
    have := pdDeRhamColumnZero_isStrictlyLE p k r
    infer_instance⟩⟩

/-- 上に有界な導来圏での完備化単位。 -/
def pdColumnZeroDerivedUnit :
    pdUncompletedColumnZeroDerived k r ⟶ pdCompletedColumnZeroDerived p k r :=
  ObjectProperty.homMk (DerivedCategory.Q.map
    (HomologicalComplex.extendMap (pdColumnCompletionUnit p k r ⦋0⦌) emb))

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- 第 0 列の自由模型の底変換同型を、整数添字へ延長する。 -/
def pdColumnZeroFreeBaseChangeIso :
    baseChange (algebraMap A B) ((pdUncompletedColumn A r ⦋0⦌).extend emb) ≅
      (pdUncompletedColumn B r ⦋0⦌).extend emb :=
  mapExtendIso (ModuleCat.extendScalars (algebraMap A B)) (pdUncompletedColumn A r ⦋0⦌) emb ≪≫
    (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} B)).mapIso
      (pdUncompletedColumnBaseChangeIso A B r ⦋0⦌)

/-- 自由模型を底変換してから標的の完備第 0 列へ送る標準余鎖写像。 -/
def pdColumnZeroBaseChangeFreeMap :
    baseChange (algebraMap A B) ((pdUncompletedColumn A r ⦋0⦌).extend emb) ⟶
      (pdDeRhamColumn p B r ⦋0⦌).extend emb :=
  (pdColumnZeroFreeBaseChangeIso r A B).hom ≫
    HomologicalComplex.extendMap (pdColumnCompletionUnit p B r ⦋0⦌) emb

variable (hA : Function.Injective (fun x : A => (p : A) * x))
variable (hB : Function.Injective (fun x : B => (p : B) * x))

/-- p 正則な二つの基底環の間では、完備第 0 列が完備導来底変換を計算する。 -/
def pdColumnZeroCompletedBaseChangeIso :
    (derivedComplexCompletionFunctor B (p : B)).obj
      ((boundedAboveDerivedBaseChange (algebraMap A B)).obj
        (pdCompletedColumnZeroDerived p A r)).obj ≅
        DerivedCategory.Q.obj ((pdDeRhamColumn p B r ⦋0⦌).extend emb) := by
  have hf : IsIso ((derivedComplexCompletionFunctor A (p : A)).map
      (pdColumnZeroDerivedUnit p A r).hom) :=
    pdColumnCompletionUnit_completion_isIso p A r ⦋0⦌ hA
  have hg : IsIso ((derivedComplexCompletionFunctor B ((algebraMap A B) (p : A))).map
      (DerivedCategory.Q.map (pdColumnZeroBaseChangeFreeMap p r A B))) := by
    rw [map_natCast]
    dsimp only [pdColumnZeroBaseChangeFreeMap]
    rw [Functor.map_comp, Functor.map_comp]
    have := pdColumnCompletionUnit_completion_isIso p B r ⦋0⦌ hB
    infer_instance
  have hT := pdDeRhamColumn_isComplete p B r 0
  have e := completedBaseChangeModelIso (algebraMap A B) (p : A)
    (pdColumnZeroDerivedUnit p A r) hf (pdUncompletedColumnZeroModel A r)
    (pdColumnZeroBaseChangeFreeMap p r A B) hg (by simpa only [map_natCast] using hT)
  simpa only [map_natCast] using e


end SerrePositivity.BhattScholze.Prismatic
