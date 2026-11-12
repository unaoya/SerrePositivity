module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.BinaryTensorInputDecomposition
public import SerrePositivity.EInfinity.BarrattEccles.Theory.BinaryTensorColorClassification
public import SerrePositivity.EInfinity.BarrattEccles.Theory.TwoColorCoefficientSource
public import SerrePositivity.EInfinity.BarrattEccles.Theory.FiniteInductionMatrix

/-!
# 二色の入力の指定成分

## 概要
HA 3.2.4.7 の自由比較のため、標準二色パターンの包含と射影を実際の二色部分群で読む。

## 方針
安定化群の同定を指定作用へ適用し、実際の入力複体から誘導・余誘導の射を作る。

## 規約
任意の複体の微分を保つ。零微分・有界性・平坦性を仮定しない。

## 使われ方
色付き Schur 分解の各 arity と各二色成分。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
variable {A : Type u} [CommRing A] (X Y : Complex A) (m n : ℕ)

/-- 二色部分群の、実際の入力位置への置換作用。 -/
def twoColorInputPermutation : TwoColorGroup.{u} m n →* Equiv.Perm (Fin (m + n)) :=
  MulEquiv.ulift.toMonoidHom.comp (twoColorPermutationHom.{u} m n).range.subtype

/-- 指定二色部分群は標準入力のパターンを固定する。 -/
lemma twoColorInputPermutation_fixed (g : TwoColorGroup.{u} m n) :
    twoColorInputPermutation m n g • binaryTensorStandardPattern m n =
      binaryTensorStandardPattern m n :=
  (binaryTensorStandard_mem_twoColor_iff m n g.val.down).mp g.property

/-- 和のテンソル冪の、全対称群上の入力表現の複体。 -/
def twoColorFullInput :
    CochainComplex (Rep.{u} A (ULift.{u} (Equiv.Perm (Fin (m + n))))) ℤ :=
  representationCochainComplex
    (binaryTensorPowerAction X Y (m + n) MulEquiv.ulift.toMonoidHom)

/-- 標準入力パターンの、指定二色部分群上の表現の複体。 -/
def twoColorStandardInput : CochainComplex (Rep.{u} A (TwoColorGroup.{u} m n)) ℤ :=
  binaryTensorWordFixedRepresentation X Y (m + n) (binaryTensorStandardPattern m n)
    (twoColorInputPermutation m n) (twoColorInputPermutation_fixed m n)

/-- 標準二色成分から実際の入力複体への指定包含。 -/
def twoColorStandardInputInclusion :
    twoColorStandardInput X Y m n ⟶
      ((Rep.resFunctor (twoColorPermutationHom.{u} m n).range.subtype).mapHomologicalComplex
        (.up ℤ)).obj (twoColorFullInput X Y m n) :=
  binaryTensorFixedRepresentationInclusion X Y (m + n) (binaryTensorStandardPattern m n)
    (twoColorInputPermutation m n) (twoColorInputPermutation_fixed m n)

/-- 実際の入力複体から標準二色成分への指定射影。 -/
def twoColorStandardInputProjection :
    ((Rep.resFunctor (twoColorPermutationHom.{u} m n).range.subtype).mapHomologicalComplex
      (.up ℤ)).obj (twoColorFullInput X Y m n) ⟶ twoColorStandardInput X Y m n :=
  binaryTensorFixedRepresentationProjection X Y (m + n) (binaryTensorStandardPattern m n)
    (twoColorInputPermutation m n) (twoColorInputPermutation_fixed m n)

/-- 二色成分の包含と射影の合成は、各次数で恒等射となる。 -/
lemma twoColorStandardInputInclusion_projection (i : ℤ) :
    (twoColorStandardInputInclusion X Y m n).f i ≫
      (twoColorStandardInputProjection X Y m n).f i = 𝟙 _ := by
  apply (forget₂ (Rep.{u} A (TwoColorGroup.{u} m n)) (ModuleCat A)).map_injective
  change (binaryTensorWordInclusion X Y (m + n) (binaryTensorStandardPattern m n)).f i ≫
    (binaryTensorWordProjection X Y (m + n) (binaryTensorStandardPattern m n)).f i = 𝟙 _
  exact congrArg (fun f => f.f i)
    (binaryTensorWordInclusion_projection X Y (m + n) (binaryTensorStandardPattern m n))

/-- 指定包含を、実際の二色部分群から誘導した入力複体の射へ延ばす。 -/
def twoColorInducedInputInclusion :=
  finiteInductionCochainInclusion (twoColorPermutationHom.{u} m n).range
    (twoColorStandardInput X Y m n) (twoColorFullInput X Y m n)
    (twoColorStandardInputInclusion X Y m n)

/-- 指定射影を、実際の二色部分群から余誘導した入力複体の射へ延ばす。 -/
def twoColorCoinducedInputProjection :=
  finiteCoinductionCochainProjection (twoColorPermutationHom.{u} m n).range
    (twoColorStandardInput X Y m n) (twoColorFullInput X Y m n)
    (twoColorStandardInputProjection X Y m n)

end SerrePositivity.EInfinity.BarrattEccles
