module

public import SerrePositivity.InfinityCategories.HomotopyLimits.ConeSpanLimitCriterion

/-!
概要：極限錐を底の pinched Hom から錐の頂点 fiber への実際の比較射で検出する。
方針：比較 span の自明 Kan fibration の切断の同値性で、始点評価の同値判定を移す。
規約：比較射には切断の選択が含まれ、既存の豊穣 Hom の q_x とまだ同定していない。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.4.1.6、7.5.4.6 の表現可能な極限の検出。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 概要：right fibration の実際の表現可能な比較がホモトピー同値であることは始点評価の同値性と同値。
方針：span の射影の切断は同値なので、比較射の分解に二対三則を使う。
規約：選んだ切断の自然性は要求しない。
使われ方：Kerodon 7.4.1.6、7.5.4.6 の写像空間を始域とする比較の同値判定。 -/
lemma rightFibrationHomComparison_homotopyEquivalence_iff {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (r : E ⟶ B) [RightFibration r]
    (c : E.obj (Opposite.op ⦋0⦌)) (x : B.obj (Opposite.op ⦋0⦌)) :
    IsSimplicialHomotopyEquivalence (rightFibrationHomComparison r c x) ↔
      IsSimplicialHomotopyEquivalence (rightFibrationMappingEvaluation r c x) := by
  have hp := isQCatEquivalence_of_trivialKanFibration (rightFibrationMappingHomProjection r c x)
  have hs : IsQCatEquivalence (rightFibrationMappingSection r c x) := by
    apply hp.cancel_right
    rw [rightFibrationMappingSection_projection]
    exact (qCatEquivalenceOfIso (Iso.refl _)).isQCatEquivalence
  constructor
  · intro h
    have hcomp : IsQCatEquivalence
        (rightFibrationMappingSection r c x ≫ rightFibrationMappingEvaluation r c x) :=
      h.isQCatEquivalence
    exact (hs.cancel_left hcomp).isSimplicialHomotopyEquivalence
  · intro h
    exact (hs.comp h.isQCatEquivalence).isSimplicialHomotopyEquivalence

/-- 概要：極限錐は全頂点 x で底の pinched Hom と錐の頂点 fiber を同値にする比較射で検出できる。
方針：実際の表現可能な比較の分解と始点評価の極限錐判定を組み合わせる。
規約：添字 K は任意。豊穣 Hom の比較射との接続はこの判定とは別途必要。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.4.1.6、7.5.4.6 の ∞ 極限の表現可能な検出。 -/
lemma isLimitCone_iff_rightFibrationHomComparison_homotopyEquivalence
    {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X} (c : JoinCone p) :
    IsLimitCone c ↔ ∀ x : X.obj (Opposite.op ⦋0⦌),
      IsSimplicialHomotopyEquivalence
        (rightFibrationHomComparison (sliceOverProjection p) c x) := by
  rw [isLimitCone_iff_mappingEvaluation_homotopyEquivalence]
  apply forall_congr'
  intro x
  exact (rightFibrationHomComparison_homotopyEquivalence_iff (sliceOverProjection p) c x).symm

end SerrePositivity.InfinityCategories.HomotopyLimits
