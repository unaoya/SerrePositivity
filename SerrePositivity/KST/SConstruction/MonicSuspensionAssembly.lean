module
public import SerrePositivity.KST.SConstruction.NaturalPointedFactorization
public import SerrePositivity.KST.SConstruction.SuspensionAssemblyNaturality

/-! # Kan 標的を持つ自然な単射 suspension の組み立て
概要：suspension の自然な比較射を、Kan 中間対象への単射と元の Kan 段への比較に分解する。
方針：標的の Kan 置換の単位と合成してから、点つき自然変換を関手的に分解する。
規約：源の模型はまだ一次方向の境界商。使われ方：BF の単射構造射への接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories

/-- 概要：suspension の組み立ての標的を点つき Kan 置換する。
方針：既存の自然変換に標的の置換の単位を合成する。
規約：源の Kan 置換はまだ行わない。使われ方：自然な単射分解の入力。 -/
def kanTargetSuspensionAssemblyNat (r : ℕ) :
    oneDirectionReducedRealizationFunctor r ⋙ tensorLeft PointedSimplicialSet.circle.{u} ⟶
      boundaryKanRealizationFunctor (r + 1) :=
  oneDirectionSuspensionAssemblyNat r ≫
    Functor.whiskerLeft (boundaryReducedRealizationFunctor (r + 1)) Spectra.PointedKanReplacement.unit

/-- 概要：suspension の単射分解の Kan 中間対象の関手。
方針：Kan 標的への自然変換に関手的分解を適用する。
規約：元の次段と自然な π_* 比較を持つ。使われ方：単射な構造射の標的模型。 -/
def monicSuspensionKanFunctor (r : ℕ) : StableModel.{u} ⥤ PointedSimplicialSet.{u} :=
  pointedTransformationMiddle (kanTargetSuspensionAssemblyNat r)

/-- 概要：suspension から Kan 中間対象への自然な単射。
方針：関手的分解の左因子を取る。
規約：源は一次方向を固定した境界商の suspension。使われ方：構造射の単射模型。 -/
def monicSuspensionAssemblyNat (r : ℕ) :
    oneDirectionReducedRealizationFunctor r ⋙ tensorLeft PointedSimplicialSet.circle.{u} ⟶
      monicSuspensionKanFunctor r :=
  pointedTransformationLeft (kanTargetSuspensionAssemblyNat r)

/-- 概要：中間 Kan 模型から元の次の Kan 境界商への自然な比較。
方針：関手的分解の右因子を取る。
規約：各成分は trivial Kan fibration。使われ方：元の反復段との比較。 -/
def monicSuspensionComparisonNat (r : ℕ) :
    monicSuspensionKanFunctor r ⟶ boundaryKanRealizationFunctor (r + 1) :=
  pointedTransformationRight (kanTargetSuspensionAssemblyNat r)

/-- 概要：単射な組み立てと次段への比較の合成は元の Kan 標的への射。
方針：自然変換の分解の合成式。
規約：厳密等号。使われ方：元の構造射の比較。 -/
lemma monicSuspensionAssembly_fac (r : ℕ) :
    monicSuspensionAssemblyNat r ≫ monicSuspensionComparisonNat r = kanTargetSuspensionAssemblyNat r :=
  pointedTransformation_fac _

/-- 概要：単射 suspension の標的模型は各入力で Kan。
方針：元の次段の Kan 性と右因子の充填性。
規約：源の Kan 性は要求しない。使われ方：構造射の Kan 標的。 -/
instance monicSuspensionKan_kanComplex (r : ℕ) (X : StableModel.{u}) :
    KanComplex (((monicSuspensionKanFunctor r).obj X).right) :=
  pointedTransformationMiddle_kanComplex (kanTargetSuspensionAssemblyNat r) X

/-- 概要：suspension の新しい組み立ては各入力で単射。
方針：左因子の単射性を使う。
規約：底の単体集合の射。使われ方：BF の構造射の単射条件への接続。 -/
instance monicSuspensionAssembly_mono (r : ℕ) (X : StableModel.{u}) :
    Mono ((monicSuspensionAssemblyNat r).app X).right :=
  pointedTransformationLeft_mono (kanTargetSuspensionAssemblyNat r) X

/-- 概要：元の次段への比較は各入力で trivial Kan fibration。
方針：右因子の全単射への右持ち上げ性。
規約：全次数の充填性。使われ方：元の反復との Kan 比較。 -/
instance monicSuspensionComparison_trivialKanFibration (r : ℕ) (X : StableModel.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration ((monicSuspensionComparisonNat r).app X).right :=
  pointedTransformationRight_trivialKanFibration (kanTargetSuspensionAssemblyNat r) X

/-- 概要：元の次段への比較は全基点・全次数で π_* 同型。
方針：Kan 標的への右因子の比較。
規約：零次数も含む。使われ方：単射な構造射の標的模型の同値性。 -/
lemma monicSuspensionComparison_piIsomorphism (r : ℕ) (X : StableModel.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((monicSuspensionComparisonNat r).app X).right :=
  pointedTransformationRight_piIsomorphism (kanTargetSuspensionAssemblyNat r) X

end SerrePositivity.KST.SConstruction
