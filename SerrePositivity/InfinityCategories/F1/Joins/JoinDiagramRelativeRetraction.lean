module

public import SerrePositivity.InfinityCategories.F1.Joins.JoinDiagramRetraction
public import SerrePositivity.InfinityCategories.Core.FatJoinComparisonNaturality

/-!
概要：部分パラメータ上の逆と両立する fat join 図式比較のレトラクション。
方針：部分族の逆を先に選び、左因子の条件とともに相対境界上から延長する。
規約：任意の単射 i ごとに逆を選び、全単射に関する自然な選択は主張しない。
使われ方：Kerodon §4.6.6、区間写像空間の比較の厳密な左逆の構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：単射な部分パラメータ上の逆と整合し、両端を保つ図式比較の左逆が存在する。
方針：部分族の逆を左右固定で選び、全族では左端と部分族を同時に保って延長する。
規約：最後の右端の固定は部分族との整合性から従い、A の非空性は不要。
使われ方：Kerodon §4.6.6、pinched 模型を固定した区間模型からの逆の選択。 -/
lemma exists_pre_fatJoinComparison_relative_retraction
    {A B : SSet.{u}} (i : A ⟶ B) [Mono i] (K X : SSet.{u}) [Quasicategory X] :
    ∃ rA : (ihom (fatJoin A K)).obj X ⟶ (ihom (join A K)).obj X,
    ∃ rB : (ihom (fatJoin B K)).obj X ⟶ (ihom (join B K)).obj X,
      (pre (fatJoinComparison A K)).app X ≫ rA = 𝟙 _ ∧
      (pre (fatJoinComparison B K)).app X ≫ rB = 𝟙 _ ∧
      rB ≫ (pre (joinMap i (𝟙 K))).app X = (pre (fatJoinMap i (𝟙 K))).app X ≫ rA ∧
      rB ≫ (pre (joinInl B K)).app X = (pre (fatJoinInl B K)).app X ∧
      rB ≫ (pre (joinInr B K)).app X = (pre (fatJoinInr B K)).app X := by
  obtain ⟨rA, hrA, hlA, hrA'⟩ := exists_pre_fatJoinComparison_retraction A K X
  let e := (pre (fatJoinComparison B K)).app X
  have he : IsPrecompositionEquivalence e :=
    (isPrecompositionEquivalence_fatJoinComparison B K X).isPrecompositionEquivalence
  let v := (pre (fatJoinMap i (𝟙 K))).app X ≫ rA
  let w := (pre (fatJoinInl B K)).app X
  have hv : e ≫ v = (𝟙 _) ≫ (pre (joinMap i (𝟙 K))).app X := by
    dsimp [e, v]
    rw [← Category.assoc, ← NatTrans.comp_app, ← pre_map,
      fatJoinComparison_naturality, pre_map, NatTrans.comp_app, Category.assoc, hrA,
      Category.comp_id, Category.id_comp]
  have hw : e ≫ w = (𝟙 _) ≫ (pre (joinInl B K)).app X := by
    dsimp [e, w]
    rw [← NatTrans.comp_app, ← pre_map, fatJoinInl_comparison, Category.id_comp]
  have hvw : v ≫ (pre (joinInl A K)).app X = w ≫ (pre i).app X := by
    dsimp [v, w]
    rw [Category.assoc, hlA, ← NatTrans.comp_app, ← pre_map, fatJoinInl_map,
      ← NatTrans.comp_app, ← pre_map]
  obtain ⟨rB, hrB, hi, hlB⟩ := exists_joinDiagramFamily_extension_of_leftBoundary
    e he i K (𝟙 _) v w hv hw hvw
  refine ⟨rA, rB, hrA, hrB, hi, hlB, ?_⟩
  have hj : (pre (joinMap i (𝟙 K))).app X ≫ (pre (joinInr A K)).app X =
      (pre (joinInr B K)).app X := by
    rw [← NatTrans.comp_app, ← pre_map, joinInr_joinMap, Category.id_comp]
  rw [← hj, ← Category.assoc, hi]
  change ((pre (fatJoinMap i (𝟙 K))).app X ≫ rA) ≫ _ = _
  rw [Category.assoc, hrA', ← NatTrans.comp_app, ← pre_map,
    fatJoinInr_map, Category.id_comp]

end SerrePositivity.InfinityCategories
