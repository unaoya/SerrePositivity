module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.JoinEndpointMaps
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.JoinLeftBoundaryExtension

/-!
概要：fat join 図式から通常の join 図式への、両端を保つ厳密なレトラクション。
方針：前合成比較の単射な同値と、両端包含への制限に対する持ち上げ性を使う。
規約：逆の選択は自然性を主張せず、必要な部分族との整合性を別途指定する。
使われ方：Kerodon §4.6.6（Tag 04HY）、区間写像空間の比較の厳密な左逆。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：fat join の前合成比較は、左右の因子を保つ厳密な左逆を持つ。
方針：両端包含の前合成に対する左持ち上げ性で逆を選ぶ。
規約：両因子は任意、X のみ quasicategory。
使われ方：Kerodon §4.6.6（Tag 04HY）、部分族の指定に用いる図式の逆。 -/
lemma exists_pre_fatJoinComparison_retraction (A K X : SSet.{u}) [Quasicategory X] :
    ∃ r : (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin A K)).obj X ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A K)).obj X,
      (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinComparison A K)).app X ≫ r = 𝟙 _ ∧
      r ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A K)).app X = (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl A K)).app X ∧
      r ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A K)).app X = (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A K)).app X := by
  let e := (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinComparison A K)).app X
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence e :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_fatJoinComparison A K X).isPrecompositionEquivalence
  have := he.hasLiftingProperty_pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInclusion A K) X
  let sq : CommSq (𝟙 _) e ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInclusion A K)).app X)
      ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinEndpointInclusion A K)).app X) := ⟨by
    dsimp [e]
    rw [Category.id_comp, ← NatTrans.comp_app, ← pre_map,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinEndpointInclusion_comparison]⟩
  refine ⟨sq.lift, sq.fac_left, ?_, ?_⟩
  · have h := congrArg (fun f ↦ f ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInl A K)).app X) sq.fac_right
    simpa only [Category.assoc, ← NatTrans.comp_app, ← pre_map,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInl_inclusion, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInl_fatInclusion] using h
  · have h := congrArg (fun f ↦ f ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInr A K)).app X) sq.fac_right
    simpa only [Category.assoc, ← NatTrans.comp_app, ← pre_map,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInr_inclusion, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInr_fatInclusion] using h

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
