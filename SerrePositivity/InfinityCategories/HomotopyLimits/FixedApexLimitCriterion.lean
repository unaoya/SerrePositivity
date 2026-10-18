module

public import SerrePositivity.InfinityCategories.HomotopyLimits.FixedSliceConeEquivalence

/-!
概要：内部 Hom の固定頂点の錐の空間を終域とする表現可能な ∞ 極限判定。
方針：right fibration の標準比較に slice の頂点 fiber の模型の同値を後合成する。
規約：既存の span の切断の選択を保持し、豊穣 Hom の比較との一致は別に扱う。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.4.1.6、7.5.4.6 の切断模型への極限判定の移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 概要：底の pinched Hom から内部 Hom の固定頂点の錐の空間への実際の表現可能な比較。
方針：right fibration の比較と固定頂点の模型の標準比較を合成する。
規約：span の自明 Kan fibration の切断の選択を含み、その自然性は主張しない。
使われ方：Kerodon 7.4.1.6、7.5.4.6 の切断空間を終域とする比較への準備。 -/
noncomputable def fixedApexConeHomComparison {K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} (c : JoinCone p) (x : X _⦋0⦌) :
    pinchedHom x c.vertex ⟶ fixedApexConeFamily p x :=
  rightFibrationHomComparison (sliceOverProjection p) c x ≫ coneVertexFiberFamilyMap p x

/-- 概要：固定頂点の内部 Hom の錐への比較の同値性は slice の頂点 fiber への比較の同値性と同値。
方針：後段の固定頂点の模型の同値性と二対三則を使う。
規約：任意の図式と全ての頂点に適用する。
使われ方：Kerodon 7.4.1.6 の表現可能な極限判定の終域の移送。 -/
lemma fixedApexConeHomComparison_homotopyEquivalence_iff {K X : SSet.{u}}
    [Quasicategory X] {p : K ⟶ X} (c : JoinCone p) (x : X _⦋0⦌) :
    IsSimplicialHomotopyEquivalence (fixedApexConeHomComparison c x) ↔
      IsSimplicialHomotopyEquivalence
        (rightFibrationHomComparison (sliceOverProjection p) c x) := by
  have he := coneVertexFiberFamilyMap_isQCatEquivalence p x
  constructor
  · intro h
    exact (he.cancel_right h.isQCatEquivalence).isSimplicialHomotopyEquivalence
  · intro h
    exact (h.isQCatEquivalence.comp he).isSimplicialHomotopyEquivalence

/-- 概要：錐の極限性は各頂点での内部 Hom の固定頂点の錐への比較のホモトピー同値性で検出できる。
方針：既存の right fibration の表現可能な極限判定を、終域の模型の同値で移す。
規約：K は任意で、coherent な全ての錐を扱う。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.4.1.6、7.5.4.6 の主比較の native な側。 -/
lemma isLimitCone_iff_fixedApexConeHomComparison_homotopyEquivalence
    {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X} (c : JoinCone p) :
    IsLimitCone c ↔ ∀ x : X _⦋0⦌,
      IsSimplicialHomotopyEquivalence (fixedApexConeHomComparison c x) := by
  rw [isLimitCone_iff_rightFibrationHomComparison_homotopyEquivalence]
  apply forall_congr'
  intro x
  exact (fixedApexConeHomComparison_homotopyEquivalence_iff c x).symm

end SerrePositivity.InfinityCategories.HomotopyLimits
