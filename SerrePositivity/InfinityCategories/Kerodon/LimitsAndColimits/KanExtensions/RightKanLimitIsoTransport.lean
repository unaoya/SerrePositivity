module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightExistence
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftPullbackLimitTransport

/-!
概要：指定した同型な Kan の添字写像は、元の右局所図式の極限と右 Kan 延長の存在を保つ。
方針：coslice 射影の left fibration に既存の引き戻しの係数移送を適用する。
規約：指定変換の構成は局所極限からの既存の存在定理を使い、値だけで代用しない。
使われ方：Kerodon Definition 7.3.1.2（Tag 02Y9）、S8 の固定 Yoneda に沿う右 Kan 延長。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
variable {K C D : SSet.{u}} [Quasicategory K] [Quasicategory C] [Quasicategory D]
  {δ δ' : K ⟶ C}

/-- 同型な添字写像の右 Kan 局所図式は、同じ係数の極限の存在が同値である。
Kerodon Definition 7.3.1.2（Tag 02Y9）、既存の coslice の引き戻しの底移送則。 -/
lemma hasLimit_rightKanDiagram_iff_of_functorIso (e : FunctorIso δ δ')
    (O : K ⟶ D) (c : C _⦋0⦌) :
    HasLimit (rightKanDiagram δ O c) ↔ HasLimit (rightKanDiagram δ' O c) :=
  hasLimit_leftPullback_iff_of_functorIso (sliceUnderProjection (SSet.yonedaEquiv.symm c)) e O

/-- 同型な添字写像の下で、指定変換を持つ右 Kan 拡張の存在を双方向に運ぶ。
Kerodon Definition 7.3.1.2（Tag 02Y9）、局所極限からの既存の全変換の構成の移送則。 -/
lemma exists_rightKanExtension_iff_of_functorIso (e : FunctorIso δ δ') (O : K ⟶ D) :
    (∃ (G : C ⟶ D) (ε : SSet.Homotopy (δ ≫ G) O), IsRightKanExtension δ O G ε) ↔
      (∃ (G : C ⟶ D) (ε : SSet.Homotopy (δ' ≫ G) O), IsRightKanExtension δ' O G ε) := by
  rw [exists_kanRightExtension_iff_local_limits, exists_kanRightExtension_iff_local_limits]
  exact forall_congr' (fun c => hasLimit_rightKanDiagram_iff_of_functorIso e O c)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
