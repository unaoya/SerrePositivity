module
public import SerrePositivity.KST.SConstruction.NaturalPointedFactorization
public import SerrePositivity.KST.SConstruction.OneDirectionWeakComparison

/-! # S₁ の境界商の比較の自然な単射 Kan 模型
概要：Kan 置換した S₁ 比較を、単射と trivial Kan fibration に自然に分解する。
方針：自然変換の点つき因子分解を適用し、両因子の π_* 同型性を示す。
規約：同値性を新しい前提にしない。使われ方：反復間の段の比較と単射模型への接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories

/-- 概要：Kan 置換した一次方向の比較の中間対象の関手。
方針：既存の自然な π_* 比較に関手的分解を適用する。
規約：全入力について Kan。使われ方：S₁ 比較の単射模型。 -/
def refinedOneDirectionKanFunctor (r : ℕ) : StableModel.{u} ⥤ PointedSimplicialSet.{u} :=
  pointedTransformationMiddle (oneDirectionKanComparisonNat r)

/-- 概要：一次方向の Kan 実現から中間 Kan 模型への自然な単射。
方針：関手的分解の左因子。
規約：各成分は π_* 同型でもある。使われ方：単射比較。 -/
def refinedOneDirectionLeftNat (r : ℕ) :
    oneDirectionKanRealizationFunctor r ⟶ refinedOneDirectionKanFunctor r :=
  pointedTransformationLeft (oneDirectionKanComparisonNat r)

/-- 概要：中間 Kan 模型から元の Kan 境界商への自然な比較。
方針：関手的分解の右因子。
規約：各成分は trivial Kan fibration。使われ方：元の反復との比較。 -/
def refinedOneDirectionRightNat (r : ℕ) :
    refinedOneDirectionKanFunctor r ⟶ boundaryKanRealizationFunctor r :=
  pointedTransformationRight (oneDirectionKanComparisonNat r)

/-- 概要：自然な二因子の合成は既存の S₁ の Kan 比較。
方針：一般の自然変換の分解の式。
規約：厳密等号。使われ方：比較の可換図式。 -/
lemma refinedOneDirection_fac (r : ℕ) :
    refinedOneDirectionLeftNat r ≫ refinedOneDirectionRightNat r = oneDirectionKanComparisonNat r :=
  pointedTransformation_fac _

/-- 概要：中間模型の各値は Kan。
方針：標的の Kan 性と右因子の充填性を使う。
規約：追加仮定なし。使われ方：π_* 比較。 -/
instance refinedOneDirectionKan_kanComplex (r : ℕ) (X : StableModel.{u}) :
    KanComplex (((refinedOneDirectionKanFunctor r).obj X).right) :=
  pointedTransformationMiddle_kanComplex (oneDirectionKanComparisonNat r) X

/-- 概要：左比較は各入力で単射。
方針：一般の分解の単射性。
規約：底の単体集合の射。使われ方：cofibration 模型への接続。 -/
instance refinedOneDirectionLeft_mono (r : ℕ) (X : StableModel.{u}) :
    Mono ((refinedOneDirectionLeftNat r).app X).right :=
  pointedTransformationLeft_mono (oneDirectionKanComparisonNat r) X

/-- 概要：右比較は各入力で trivial Kan fibration。
方針：一般の分解の全単射への右持ち上げ性。
規約：標的の Kan 性の追加前提なし。使われ方：比較と持ち上げ。 -/
instance refinedOneDirectionRight_trivialKanFibration (r : ℕ) (X : StableModel.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration ((refinedOneDirectionRightNat r).app X).right :=
  pointedTransformationRight_trivialKanFibration (oneDirectionKanComparisonNat r) X

/-- 概要：右比較は全基点・全次数で π_* 同型。
方針：一般の Kan 標的への右因子の比較を使う。
規約：零次数も含む。使われ方：元の Kan 模型との同値比較。 -/
lemma refinedOneDirectionRight_piIsomorphism (r : ℕ) (X : StableModel.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((refinedOneDirectionRightNat r).app X).right :=
  pointedTransformationRight_piIsomorphism (oneDirectionKanComparisonNat r) X

/-- 概要：単射な左比較も全基点・全次数で π_* 同型。
方針：既存の S₁ 比較の π_* 同型性と右因子を打ち消す。
規約：同値性を追加仮定しない。使われ方：自然な単射模型の比較。 -/
lemma refinedOneDirectionLeft_piIsomorphism (r : ℕ) (X : StableModel.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((refinedOneDirectionLeftNat r).app X).right :=
  pointedTransformationLeft_piIsomorphism (oneDirectionKanComparisonNat r) X
    (oneDirectionReducedComparison_kan_piIsomorphism r X)

end SerrePositivity.KST.SConstruction
