module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.KanCoconeColimits
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneKanReplacement
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：非 Kan な単体集合の anodyne な Kan 置換と Kan 対象への写像空間の比較。
方針：境界との pushout-product の anodyne 性を内部 Hom の随伴で移し、全境界を持ち上げる。
規約：置換の始域の Kan 性もモデル構造の追加仮定も要求しない。
使われ方：HTT 4.2.4.1、Kan とは限らない押し出しの homotopy 余極限への移送。

対応節は Kerodon 3.1（Tag 00SZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet HomotopicalAlgebra
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
noncomputable section

/-- 概要：anodyne 射に沿う Kan 対象への内部 Hom の前合成は trivial Kan fibration。
方針：全境界との pushout-product の anodyne 性を内部 Hom の二変数随伴で移す。
規約：始域 A と終域 B の Kan 性は不要。
使われ方：HTT 4.2.4.1、非 Kan な余極限対象の Kan 置換の写像空間の比較。 -/
@[kerodon 00UT]
lemma trivialKanFibration_pre_of_anodyne {A B : SSet.{u}} (i : A ⟶ B)
    (hi : SSet.anodyneExtensions i) (X : SSet.{u}) [KanComplex X] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration ((pre i).app X) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).2
  intro n
  let sq := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) i (boundary n).ι
  let sq' := Functor.PullbackObjObj.ofIsTerminal internalHom i (terminal.from X) terminalIsTerminal
  change HasLiftingProperty (boundary n).ι sq'.π
  rw [← internalHomAdjunction₂.hasLiftingProperty_iff sq sq']
  exact (anodyneExtensions_pushoutObjObjι' sq hi) (terminal.from X)
    (by rw [← HomotopicalAlgebra.fibration_iff]; infer_instance)

/-- 概要：anodyne 射による Kan 対象への前合成は実際の単体的ホモトピー同値。
方針：trivial Kan fibration の同値性を Kan な内部 Hom のホモトピー同値へ移す。
規約：始域の二つの単体集合に充填性を仮定しない。
使われ方：Kerodon 7.5.4.6（Tag 03BB）、Kan 置換前後の錐の Hom 比較。 -/
@[kerodon 00UP]
lemma homotopyEquivalence_pre_of_anodyne {A B : SSet.{u}} (i : A ⟶ B)
    (hi : SSet.anodyneExtensions i) (X : SSet.{u}) [KanComplex X] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence ((pre i).app X) := by
  have := trivialKanFibration_pre_of_anodyne i hi X
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration _).isSimplicialHomotopyEquivalence

/-- 概要：任意の単体集合をホーンの小対象論法の値による Kan 対象に束縛する。
方針：既存の関手的 anodyne 置換の終対象への右持ち上げ性を Kan 性として読む。
規約：元の単体集合に Kan 性を仮定しない。
使われ方：HTT 4.2.4.1、実際の homotopy 押し出し対象の Kan 置換。 -/
@[kerodon 00UW]
def anodyneKanObject (A : SSet.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} := by
  let R := SerrePositivity.SimplicialModel.AnodyneKanReplacement.functor
  have : KanComplex (R.obj A) :=
    (SSet.modelCategoryQuillen.fibration_iff _).mpr
      (SerrePositivity.SimplicialModel.AnodyneKanReplacement.terminal_rlp A)
  exact ⟨R.obj A, this⟩

/-- 概要：任意の単体集合からその Kan 置換への元の比較射。
方針：既存の関手的な小対象論法の単位を使う。
規約：始域を Kan 対象に束縛しない。
使われ方：homotopy 押し出しの包含射の定義と比較。 -/
def anodyneKanObjectUnit (A : SSet.{u}) : A ⟶ (anodyneKanObject A).obj :=
  SerrePositivity.SimplicialModel.AnodyneKanReplacement.unit.app A

/-- 概要：任意の単体集合から Kan 置換への比較射は anodyne。
方針：ホーンの小対象論法の左因子の性質を使う。
規約：置換の実際の単位射の性質として述べる。
使われ方：Kan 対象への内部 Hom の前合成の比較の入力。 -/
@[kerodon 00UW]
lemma anodyneKanObjectUnit_anodyne (A : SSet.{u}) :
    SSet.anodyneExtensions (anodyneKanObjectUnit A) :=
  SerrePositivity.SimplicialModel.AnodyneKanReplacement.unit_anodyne A

/-- 概要：Kan 置換の単位による Kan 対象への前合成は trivial Kan fibration。
方針：単位の anodyne 性を全境界の持ち上げの判定へ渡す。
規約：対象 X は任意の Kan 複体。
使われ方：HTT 4.2.4.1、通常の余極限の Kan 置換の写像空間の普遍性。 -/
instance anodyneKanObjectUnit_pre_trivialKanFibration (A : SSet.{u})
    (X : SSet.{u}) [KanComplex X] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration ((pre (anodyneKanObjectUnit A)).app X) :=
  trivialKanFibration_pre_of_anodyne _ (anodyneKanObjectUnit_anodyne A) X

end
end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
