module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionRelativeLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PrecompositionTensor
public import Mathlib.CategoryTheory.LiftingProperties.Adjunction
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：単射な圏論的同値に対する右持ち上げ条件を相対 Kan 構成の入力としてまとめる。
方針：既存の前合成同値を用い、inner 性と内部 Hom による保存を証明する。
規約：標準 isofibration との比較や因子分解はこの定義から仮定しない。
使われ方：関手の制限に限らない標的上の相対図式の組み立て。

対応節は Kerodon 4.4（Tag 01EM）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations

/-- 概要：全ての単射な前合成同値を右に持ち上げる条件。
方針：任意の単体集合間の射の持ち上げ性を量化する。
規約：モデル圏の構造や充填の選択データは含めない。
使われ方：一般の標的上で相対 Kan 図式を構成するための操作的入力。 -/
@[kerodon 01FV]
def EquivalenceLifting {D E : SSet.{u}} (U : D ⟶ E) : Prop :=
  ∀ {A B : SSet.{u}} (i : A ⟶ B), Mono i → _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence i →
    HasLiftingProperty i U

/-- 概要：単射による関手の制限は単射な前合成同値を右に持ち上げる。
方針：内部 Hom の二変数の持ち上げ性の交換を使う既存の判定を適用する。
規約：標的 X のみ quasicategory とする。
使われ方：既存の境界固定の構成を一般の持ち上げ条件へ接続する。 -/
@[kerodon 01F3]
lemma equivalenceLifting_pre {A B X : SSet.{u}} [Quasicategory X]
    (i : A ⟶ B) [Mono i] : EquivalenceLifting ((pre i).app X) := by
  intro K L j hj he
  have : Mono j := hj
  exact he.hasLiftingProperty_pre i X

/-- 概要：単射な圏論的同値の右持ち上げ条件は inner fibration 性を含意する。
方針：inner horn の包含は単射な inner anodyne 射であり前合成同値である。
規約：両端の quasicategory 性を要求しない。
使われ方：一般の相対 Kan 比較に必要な内ホーン充填。 -/
lemma EquivalenceLifting.innerFibration {D E : SSet.{u}} {U : D ⟶ E}
    (hU : EquivalenceLifting U) : InnerFibration U where
  mem := by
    intro A B i hi
    cases hi with
    | intro j h0 hn =>
      exact hU _ inferInstance
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_of_innerAnodyne _ (innerAnodyneExtensions.horn_ι h0 hn))

/-- 概要：単射な圏論的同値の右持ち上げ条件は任意の内部 Hom で保存される。
方針：閉構造の随伴で左直積に移し、前合成同値の直積による保存を使う。
規約：パラメータ K に quasicategory 性を要求しない。
使われ方：後合成の fiber の可逆辺の持ち上げ条件を供給する。 -/
@[kerodon 01G4, kerodon 01H7]
lemma EquivalenceLifting.internalHom {D E : SSet.{u}} {U : D ⟶ E}
    (hU : EquivalenceLifting U) (K : SSet.{u}) :
    EquivalenceLifting ((ihom K).map U) := by
  intro A B i hi he
  have : Mono i := hi
  exact ((ihom.adjunction K).hasLiftingProperty_iff i U).mp
    (hU (K ◁ i) ((tensorLeft K).map_mono i) (he.whiskerLeft K))

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
