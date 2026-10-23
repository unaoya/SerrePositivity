module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.ScaffoldLargeOverIsos
public import SerrePositivity.InfinityCategories.F1.Scaffold.ScaffoldBridgeHomPullbacks
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalDiagramAnodyneRestriction
public import SerrePositivity.InfinityCategories.F1.Cocartesian.StraighteningHomInterval

/-!
概要：同じ分類図式の区間 Hom を、全次元で最初の辺と尾部の pullback へ制限する。
方針：同じ大きい比較への制限と厳密 pullback 表示を合成する。
規約：元の分類図式と両端固定の全パラメーターを保持する。
使われ方：高次単体の元の分類 Hom 作用の同値性を反映する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

variable (n : ℕ) {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin (n + 2)) ⥤ C)
  (p q : CocartesianFibrationCategory (nerve C))
local notation "P" => cocartesianStrictTransportCoherentDiagram p.val.hom
local notation "Q" => cocartesianStrictTransportCoherentDiagram q.val.hom
local notation "H" => cocartesianScaffoldLargeBridge n k

/-- 同じ分類図式間の全区間 Hom から、最初の区間と尾部の厳密 pullback への射。 -/
def cocartesianScaffoldTargetSegalMap :
    intervalMappingSpace (functorVertex P) (functorVertex Q) ⟶
      pullback (intervalDiagramOverPre P Q (ScaffoldBridgeOver.toFirst n H))
        (intervalDiagramOverPre P Q (ScaffoldBridgeOver.toTail n H)) :=
  intervalDiagramRestriction H P Q ≫
    (ScaffoldBridgeOver.intervalDiagram_isPullback n H P Q).isoPullback.hom

/-- 同じ target Segal 射の最初の射影は、元の同じ区間への直接制限。 -/
lemma cocartesianScaffoldTargetSegalMap_fst :
    cocartesianScaffoldTargetSegalMap n k p q ≫ pullback.fst _ _ =
      intervalDiagramRestriction (ScaffoldBridgeOver.first n H).hom P Q := by
  rw [cocartesianScaffoldTargetSegalMap, Category.assoc, IsPullback.isoPullback_hom_fst]
  exact intervalDiagramOverPre_restriction P Q (ScaffoldBridgeOver.firstInclusion n H)

/-- 同じ target Segal 射の尾部射影も、元の同じ尾部への直接制限。 -/
lemma cocartesianScaffoldTargetSegalMap_snd :
    cocartesianScaffoldTargetSegalMap n k p q ≫ pullback.snd _ _ =
      intervalDiagramRestriction (ScaffoldBridgeOver.tail n H).hom P Q := by
  rw [cocartesianScaffoldTargetSegalMap, Category.assoc, IsPullback.isoPullback_hom_snd]
  exact intervalDiagramOverPre_restriction P Q (ScaffoldBridgeOver.tailInclusion n H)

/-- 全次元で、恒等セル上の同じ target Segal 制限は自明 Kan。 -/
lemma cocartesianScaffoldTargetSegalMap_id_trivialKanFibration
    (p q : CocartesianFibrationCategory (nerve (ULift.{u} (Fin (n + 2))))) :
    TrivialKanFibration (cocartesianScaffoldTargetSegalMap n (𝟭 _) p q) := by
  have h := intervalDiagramRestriction_trivialKanFibration_of_innerAnodyne
    (cocartesianScaffoldLargeBridge n (𝟭 (ULift.{u} (Fin (n + 2)))))
    (cocartesianScaffoldLargeBridge_id_innerAnodyne n)
    (cocartesianStrictTransportCoherentDiagram p.val.hom)
    (cocartesianStrictTransportCoherentDiagram q.val.hom)
  exact ⟨trivialKanFibrations.comp_mem _ _ h.mem (trivialKanFibrations.of_isIso _)⟩

end SerrePositivity.InfinityCategories
