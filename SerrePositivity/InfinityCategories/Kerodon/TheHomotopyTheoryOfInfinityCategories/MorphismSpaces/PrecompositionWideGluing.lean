module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.WideRelativeLifting

/-!
概要：単射の wide pushout 図式の自然な比較の前合成の同値条件。
方針：比較を可逆な写像円柱の単射に置き換え、相対比較の持ち上げを余極限へ貼る。
規約：比較の成分は単射でなくてよい。各枝の射と両関手の単射保存を要求する。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の各次元のセルの族の比較。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：単射の wide pushout 図式の各対象で自然な比較が同値条件を満たせば余極限でも満たす。
方針：自然な写像円柱の単射の境界の前合成への左持ち上げ性を各枝の相対比較から貼る。
規約：二つの関手は単射と wide pushout の余極限を保つ。比較射の単射性は不要。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） のセルの族の貼り合わせ。 -/
lemma isPrecompositionEquivalence_of_widePushout_colimit
    (J : Type u) {F G : SSet.{u} ⥤ SSet.{u}} (t : F ⟶ G)
    [F.PreservesMonomorphisms] [G.PreservesMonomorphisms]
    [PreservesColimitsOfShape (WidePushoutShape J) F] [PreservesColimitsOfShape (WidePushoutShape J) G]
    (D : WidePushoutShape J ⥤ SSet.{u}) [∀ j, Mono (D.map (.init j))]
    (c : Cocone D) (hc : IsColimit c)
    (ht : ∀ n, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (t.app (D.obj n))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (t.app c.pt) := by
  let H := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.naturalEquivalenceCylinder t
  let s := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.naturalEquivalenceCylinderIn t
  let s' := Functor.whiskerLeft D s
  let cF := F.mapCocone c
  let cH := H.mapCocone c
  have hcF : IsColimit cF := isColimitOfPreserves F hc
  have hcH : IsColimit cH := isColimitOfPreserves H hc
  have hi : ∀ n, cF.ι.app n ≫ s.app c.pt = s'.app n ≫ cH.ι.app n := by
    intro n
    exact s.naturality (c.ι.app n)
  have h0 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (s'.app none) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_iff_equivalenceMappingCylinderIn _).1 (ht none)
  have : Mono (s'.app none) := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceMappingCylinderIn_mono _
  have hCorners : ∀ n, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.monoPrecompositionEquivalences (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.wideNatTransCornerMap s' n) := by
    intro n
    let α := WidePushoutShape.Hom.init n
    have : Mono (D.map α) := inferInstance
    have : Mono (F.map (D.map α)) := F.map_mono _
    have : Mono (G.map (D.map α)) := G.map_mono _
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.monoPrecompositionEquivalences
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.equivalenceMappingCylinderCornerMap (t.app (D.obj none)) (t.app (D.obj (some n)))
        (F.map (D.map α)) (G.map (D.map α)) (t.naturality (D.map α)).symm)
    exact ⟨inferInstance, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_equivalenceMappingCylinderCornerMap
      _ _ _ _ _ (ht none) (ht (some n))⟩
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_iff_equivalenceMappingCylinderIn _).2
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_iff_llp_boundaryTests _).2
  intro E Y p hp
  have : HasLiftingProperty (s'.app none) p :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_iff_llp_boundaryTests _).1 h0 _ hp
  have : ∀ n, HasLiftingProperty (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.wideNatTransCornerMap s' n) p := by
    intro n
    have : Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.wideNatTransCornerMap s' n) := (hCorners n).1
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_iff_llp_boundaryTests _).1 (hCorners n).2 _ hp
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.hasLiftingProperty_of_widePushout_relative_corners s' cF cH hcF hcH (s.app c.pt) hi p

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
