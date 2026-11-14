module
public meta import SerrePositivity.Util.Citation

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittToSmallCompletedBridge
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.PDDeRham.PDDeRhamDerivedSpan
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.PDDeRham.PDColumnCompletedBaseChange
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.PDDeRham.PDDeRhamDerivedSpan
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamCech
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.PDDeRham.PDColumnCompletedBaseChange
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.PDDeRham.PDColumnCompletionEquivalence
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDRawColumnBoundedModel
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.CompletedCechCoefficientMap
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCompletedCech
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.Algebra

/-!
# 大きい Witt 分冪模型の完備導来底変換の有限射影模型

## 概要
大きい分冪 Čech 模型を第 0 列の有限な射影模型へ移し、第 0 Witt 成分による完備導来底変換を計算する。

## 方針
枠の比較と総複体の二射影で模型を固定する。古典的な底変換は未完備第 0 列の射影模型に適用し、
完備化後の標準写像との可換性を `completedBaseChangeModelIso_hom_comm` で記録する。

## 規約
計算に使う各項は射影的な未完備第 0 列。源と標的の p 正則性は既存の列の完備化比較に明記される。
完備化元は第 0 Witt 成分で写した p であり、環射なので剰余係数環の p に等しい。

## 使われ方
BS 著者版 Theorem 6.4 のWitt 係数から小さい模型への比較の実際の完備導来底変換。
-/

public noncomputable section
open CategoryTheory AlgebraicTopology
open scoped Simplicial
open SerrePositivity.DerivedCompletion
universe u
namespace SerrePositivity.BhattScholze.Prismatic
set_option backward.isDefEq.respectTransparency false
attribute [local instance] HasDerivedCategory.standard
local notation "emb" => ComplexShape.embeddingUpNat

section Generic
variable (p : ℕ) (k : Type u) [CommRing k] (r : ℕ)

/-- 小さい分冪 Čech 模型を、枠の台加群関手による交代余面複体として読む。 -/
def pdCechCochainComplex : CochainComplex (ModuleCat.{u} k) ℕ :=
  (alternatingCofaceMapComplex (ModuleCat k)).obj (pdModel p k r ⋙ PDCechNerve.algebraModule k)

/-- 第 0 列から小さい Čech 複体への比較は、総複体の二射影で固定する。 -/
def pdColumnCechDerivedIso :
    (pdCompletedColumnZeroDerived p k r).obj ≅
      DerivedCategory.Q.obj ((pdCechCochainComplex p k r).extend emb) := by
  let e := pdDeRhamRowZeroIso p k r ≪≫
    (alternatingCofaceMapComplex (ModuleCat k)).mapIso
      (underCechModuleIso k (pdModel p k r)).symm
  exact pdDeRhamDerivedColumnRowIso p k r ≪≫
    DerivedCategory.Q.mapIso (((emb).extendFunctor (ModuleCat k)).mapIso e)

private theorem cech_isLE :
    (DerivedCategory.Q.obj ((pdCechCochainComplex p k r).extend emb)).IsLE (r : ℤ) := by
  let : (pdCompletedColumnZeroDerived p k r).obj.IsLE (r : ℤ) := by
    have := pdDeRhamColumnZero_isStrictlyLE p k r
    change (DerivedCategory.Q.obj
      ((pdDeRhamColumn p k r ⦋0⦌).extend emb)).IsLE (r : ℤ)
    infer_instance
  exact DerivedCategory.TStructure.t.isLE_of_iso (pdColumnCechDerivedIso p k r) r

/-- 小さい分冪 Čech 複体を、上に有界な導来対象として読む。 -/
def pdCechMinus : DerivedCategory.Minus (ModuleCat.{u} k) :=
  ⟨DerivedCategory.Q.obj ((pdCechCochainComplex p k r).extend emb), ⟨r, cech_isLE p k r⟩⟩
end Generic

section Witt
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)
variable (hpC : Function.Injective (fun x : A ⧸ P.ideal => (p : A ⧸ P.ideal) * x))
variable (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A ⧸ P.ideal))
variable [hC : IsAdicComplete (Ideal.span {(p : A ⧸ P.ideal)}) (A ⧸ P.ideal)]
variable (T : Poly (A ⧸ P.ideal))
local notation "C" => A ⧸ P.ideal
local notation "W" => WittVector p C
local instance : Algebra W C := (wZero p C).toAlgebra
local notation "F" => derivedComplexCompletionFunctor C ((wZero p C) (p : W))
local notation "L" => boundedAboveDerivedBaseChange (wZero p C)

/-- 大きい Witt 分冪枠の交代余面複体。 -/
def wittBigPDCochainComplex : CochainComplex (ModuleCat.{u} W) ℕ :=
  (alternatingCofaceMapComplex (ModuleCat W)).obj
    ((wittBigPdModel P hpC hlocal).obj T ⋙ PDCechNerve.algebraModule W)

/-- 有限・大きい分冪枠の比較を、整数添字の導来圏で読む。 -/
def wittPDFrameDerivedIso :
    DerivedCategory.Q.obj ((pdCechCochainComplex p W T.n).extend emb) ≅
      DerivedCategory.Q.obj ((wittBigPDCochainComplex P hpC hlocal T).extend emb) := by
  have := wittSmallFrame_quasiIso P hpC hlocal T hC
  exact asIso (DerivedCategory.Q.map (HomologicalComplex.extendMap
    ((alternatingCofaceMapComplex (ModuleCat W)).map
      (Functor.whiskerRight (wittSmallFrame P hpC hlocal T hC) (PDCechNerve.algebraModule W))) emb))

private theorem big_isLE :
    (DerivedCategory.Q.obj
      ((wittBigPDCochainComplex P hpC hlocal T).extend emb)).IsLE (T.n : ℤ) := by
  let := cech_isLE p W T.n
  exact DerivedCategory.TStructure.t.isLE_of_iso (wittPDFrameDerivedIso P hpC hlocal T) T.n

/-- 大きい Witt 分冪 Čech 複体は、変数の数を上限とする導来対象。 -/
def wittBigPDMinus : DerivedCategory.Minus (ModuleCat.{u} W) :=
  ⟨DerivedCategory.Q.obj ((wittBigPDCochainComplex P hpC hlocal T).extend emb),
    ⟨T.n, big_isLE P hpC hlocal T⟩⟩

/-- 第 0 列から大きい Witt 分冪模型への、枠と二射影で固定した導来同型。 -/
def wittBigPDColumnIso :
    pdCompletedColumnZeroDerived p W T.n ≅ wittBigPDMinus P hpC hlocal T :=
  ObjectProperty.isoMk _ (pdColumnCechDerivedIso p W T.n ≪≫ wittPDFrameDerivedIso P hpC hlocal T)

/-- 未完備第 0 列の実際の複体を、そのまま上に有界な導来対象として読む。 -/
@[expose] def wittToSmallRawColumnMinus : DerivedCategory.Minus (ModuleCat.{u} W) :=
  ⟨DerivedCategory.Q.obj
    ((pdUncompletedColumn W T.n ⦋0⦌).extend ComplexShape.embeddingUpNat),
    ⟨T.n, by
      have := pdUncompletedColumnZero_isStrictlyLE W T.n
      infer_instance⟩⟩

/-- 未完備の有限第 0 列を、大きい分冪模型の完備導来模型へ送る標準写像。 -/
def wittBigPDColumnModelUnit :
    wittToSmallRawColumnMinus P T ⟶ wittBigPDMinus P hpC hlocal T :=
  pdColumnZeroDerivedUnit p W T.n ≫ (wittBigPDColumnIso P hpC hlocal T).hom

private theorem modelUnit_completed_isIso :
    IsIso ((derivedComplexCompletionFunctor W (p : W)).map
      (wittBigPDColumnModelUnit P hpC hlocal T).hom) := by
  change IsIso ((derivedComplexCompletionFunctor W (p : W)).map
    ((pdColumnZeroDerivedUnit p W T.n).hom ≫ (wittBigPDColumnIso P hpC hlocal T).hom.hom))
  rw [CategoryTheory.Functor.map_comp]
  let : IsIso ((derivedComplexCompletionFunctor W (p : W)).map
      (pdColumnZeroDerivedUnit p W T.n).hom) :=
    pdColumnCompletionUnit_completion_isIso p W T.n ⦋0⦌
      (witt_mul_prime_injective p C hpC)
  let : IsIso (wittBigPDColumnIso P hpC hlocal T).hom.hom := by
    change IsIso ((DerivedCategory.Minus.ι).map
      (wittBigPDColumnIso P hpC hlocal T).hom)
    infer_instance
  infer_instance

/-- 実際の未完備第 0 列を使う射影模型。公開型から複体の各項を直接参照できる。 -/
@[expose] def wittToSmallDerivedModel :
    BoundedAboveDerivedModel (wittToSmallRawColumnMinus P T).obj where
  complex := (pdUncompletedColumn W T.n ⦋0⦌).extend ComplexShape.embeddingUpNat
  bound := T.n
  bounded := pdUncompletedColumnZero_isStrictlyLE W T.n
  projective := pdUncompletedColumnZero_projective W T.n
  iso := Iso.refl _

omit hC in
/-- 導来底変換に使う未完備列の各項は射影的。 -/
theorem wittToSmallDerivedModel_projective (i : ℤ) :
    Projective ((wittToSmallDerivedModel P T).complex.X i) :=
  (wittToSmallDerivedModel P T).projective i

include hpC in
omit hC in
private theorem freeMap_completed_isIso :
    IsIso ((F).map (DerivedCategory.Q.map (pdColumnZeroBaseChangeFreeMap p T.n W C))) := by
  rw [map_natCast]
  dsimp only [pdColumnZeroBaseChangeFreeMap]
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  have := pdColumnCompletionUnit_completion_isIso p C T.n ⦋0⦌ hpC
  infer_instance

omit hC in
private theorem targetColumnComplete :
    IsComplete C ((wZero p C) (p : W))
      (DerivedCategory.Q.obj ((pdDeRhamColumn p C T.n ⦋0⦌).extend emb)) := by
  rw [map_natCast]
  exact pdDeRhamColumn_isComplete p C T.n 0

/-- 第 0 Witt 成分による大きい分冪模型の完備導来底変換を、有限第 0 列で計算する。 -/
def wittToSmallDerivedCompletedColumnIso :
    (F).obj ((L).obj (wittBigPDMinus P hpC hlocal T)).obj ≅
      DerivedCategory.Q.obj ((pdDeRhamColumn p C T.n ⦋0⦌).extend emb) :=
  completedBaseChangeModelIso (wZero p C) (p : W)
    (wittBigPDColumnModelUnit P hpC hlocal T) (modelUnit_completed_isIso P hpC hlocal T)
    (wittToSmallDerivedModel P T) (pdColumnZeroBaseChangeFreeMap p T.n W C)
    (freeMap_completed_isIso P hpC T) (targetColumnComplete P T)

/-- 大きい分冪模型の完備導来底変換から小さい分冪 Čech 模型への比較同型。 -/
def wittToSmallDerivedCompletedIso :
    (F).obj ((L).obj (wittBigPDMinus P hpC hlocal T)).obj ≅ (pdCechMinus p C T.n).obj :=
  wittToSmallDerivedCompletedColumnIso P hpC hlocal T ≪≫ pdColumnCechDerivedIso p C T.n

/-- 有限射影模型から来る実際の係数射の完備化と、導来比較同型との可換性。 -/
theorem wittToSmallDerivedCompletedColumnIso_model_comm :
    (F).map ((L).map (wittBigPDColumnModelUnit P hpC hlocal T)).hom ≫
      (wittToSmallDerivedCompletedColumnIso P hpC hlocal T).hom ≫
      (derivedComplexCompletionUnit C ((wZero p C) (p : W))).app
        (DerivedCategory.Q.obj ((pdDeRhamColumn p C T.n ⦋0⦌).extend emb)) =
    (F).map ((boundedAboveDerivedBaseChangeModelIso (wZero p C)
      (wittToSmallRawColumnMinus P T) (wittToSmallDerivedModel P T)).hom ≫
        DerivedCategory.Q.map (pdColumnZeroBaseChangeFreeMap p T.n W C)) := by
  exact completedBaseChangeModelIso_hom_comm (wZero p C) (p : W)
    (wittBigPDColumnModelUnit P hpC hlocal T) (modelUnit_completed_isIso P hpC hlocal T)
    (wittToSmallDerivedModel P T) (pdColumnZeroBaseChangeFreeMap p T.n W C)
    (freeMap_completed_isIso P hpC T) (targetColumnComplete P T)
end Witt
end SerrePositivity.BhattScholze.Prismatic

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Thm 6.4" (partial := component) "Witt の結晶 prism と、普遍基底での比較の部品（BS-D69 P2）。関手としての同型（D69）の組み立ては drafts ／ 11-11 更新。Witt 系は A と A/I が p 正則な一般の有界向き付き prism について作られている ／ 11-12 夜更新（§5・§6 の見直し）"] _root_.SerrePositivity.BhattScholze.Prismatic.wittToSmallDerivedCompletedIso
