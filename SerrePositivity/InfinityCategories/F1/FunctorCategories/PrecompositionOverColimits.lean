module

public import SerrePositivity.InfinityCategories.Core.PrecompositionSequentialGluing
public import SerrePositivity.InfinityCategories.Core.PrecompositionWideGluing
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
概要：Over 圏上の自然な比較の骨格列とセルの族での貼り合わせ。
方針：自然な可逆円柱の相対境界の持ち上げを各項から余極限へ貼る。
規約：比較の成分には単射性を要求しない。
使われ方：Kerodon Proposition 5.2.4.5、固定した底上の円柱比較のセルによる拡張。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：単射の可算列の各対象で自然な比較が同値条件を満たせば余極限でも満たす。
方針：自然な写像円柱の単射の境界の前合成への左持ち上げ性を各相対段階から貼る。
規約：始域は Over S。二つの関手は単射と自然数の余極限を保つ。比較射の単射性は不要。
使われ方：Kerodon Proposition 5.2.4.5 の骨格の余極限。 -/
lemma isPrecompositionEquivalence_over_of_sequential_colimit {S : SSet.{u}}
    {F G : Over S ⥤ SSet.{u}} (t : F ⟶ G)
    [F.PreservesMonomorphisms] [G.PreservesMonomorphisms]
    [PreservesColimitsOfShape ℕ F] [PreservesColimitsOfShape ℕ G]
    (D : ℕ ⥤ Over S) [∀ n, Mono (D.map (homOfLE (Nat.le_succ n)))]
    (c : Cocone D) (hc : IsColimit c)
    (ht : ∀ n, IsPrecompositionEquivalence (t.app (D.obj n))) :
    IsPrecompositionEquivalence (t.app c.pt) := by
  let H := naturalEquivalenceCylinder t
  let s := naturalEquivalenceCylinderIn t
  let s' := Functor.whiskerLeft D s
  let cF := F.mapCocone c
  let cH := H.mapCocone c
  have hcF : IsColimit cF := isColimitOfPreserves F hc
  have hcH : IsColimit cH := isColimitOfPreserves H hc
  have hi : ∀ n, cF.ι.app n ≫ s.app c.pt = s'.app n ≫ cH.ι.app n := by
    intro n
    exact s.naturality (c.ι.app n)
  have h0 : IsPrecompositionEquivalence (s'.app 0) :=
    (isPrecompositionEquivalence_iff_equivalenceMappingCylinderIn _).1 (ht 0)
  have : Mono (s'.app 0) := equivalenceMappingCylinderIn_mono _
  have hCorners : ∀ n, monoPrecompositionEquivalences (sequentialNatTransCornerMap s' n) := by
    intro n
    let α : n ⟶ n + 1 := homOfLE (Nat.le_succ n)
    have : Mono (D.map α) := inferInstance
    have : Mono (F.map (D.map α)) := F.map_mono _
    have : Mono (G.map (D.map α)) := G.map_mono _
    change monoPrecompositionEquivalences
      (equivalenceMappingCylinderCornerMap (t.app (D.obj n)) (t.app (D.obj (n + 1)))
        (F.map (D.map α)) (G.map (D.map α)) (t.naturality (D.map α)).symm)
    exact ⟨inferInstance, isPrecompositionEquivalence_equivalenceMappingCylinderCornerMap
      _ _ _ _ _ (ht n) (ht (n + 1))⟩
  apply (isPrecompositionEquivalence_iff_equivalenceMappingCylinderIn _).2
  apply (isPrecompositionEquivalence_iff_llp_boundaryTests _).2
  intro E Y p hp
  have : HasLiftingProperty (s'.app 0) p :=
    (isPrecompositionEquivalence_iff_llp_boundaryTests _).1 h0 _ hp
  have : ∀ n, HasLiftingProperty (sequentialNatTransCornerMap s' n) p := by
    intro n
    have : Mono (sequentialNatTransCornerMap s' n) := (hCorners n).1
    exact (isPrecompositionEquivalence_iff_llp_boundaryTests _).1 (hCorners n).2 _ hp
  exact hasLiftingProperty_of_sequential_relative_corners s' cF cH hcF hcH (s.app c.pt) hi p


/-- 概要：単射の wide pushout 図式の各対象で自然な比較が同値条件を満たせば余極限でも満たす。
方針：自然な写像円柱の単射の境界の前合成への左持ち上げ性を各枝の相対比較から貼る。
規約：始域は Over S。二つの関手は単射と wide pushout の余極限を保つ。比較射の単射性は不要。
使われ方：Kerodon Proposition 5.2.4.5 のセルの族の貼り合わせ。 -/
lemma isPrecompositionEquivalence_over_of_widePushout_colimit {S : SSet.{u}}
    (J : Type u) {F G : Over S ⥤ SSet.{u}} (t : F ⟶ G)
    [F.PreservesMonomorphisms] [G.PreservesMonomorphisms]
    [PreservesColimitsOfShape (WidePushoutShape J) F] [PreservesColimitsOfShape (WidePushoutShape J) G]
    (D : WidePushoutShape J ⥤ Over S) [∀ j, Mono (D.map (.init j))]
    (c : Cocone D) (hc : IsColimit c)
    (ht : ∀ n, IsPrecompositionEquivalence (t.app (D.obj n))) :
    IsPrecompositionEquivalence (t.app c.pt) := by
  let H := naturalEquivalenceCylinder t
  let s := naturalEquivalenceCylinderIn t
  let s' := Functor.whiskerLeft D s
  let cF := F.mapCocone c
  let cH := H.mapCocone c
  have hcF : IsColimit cF := isColimitOfPreserves F hc
  have hcH : IsColimit cH := isColimitOfPreserves H hc
  have hi : ∀ n, cF.ι.app n ≫ s.app c.pt = s'.app n ≫ cH.ι.app n := by
    intro n
    exact s.naturality (c.ι.app n)
  have h0 : IsPrecompositionEquivalence (s'.app none) :=
    (isPrecompositionEquivalence_iff_equivalenceMappingCylinderIn _).1 (ht none)
  have : Mono (s'.app none) := equivalenceMappingCylinderIn_mono _
  have hCorners : ∀ n, monoPrecompositionEquivalences (wideNatTransCornerMap s' n) := by
    intro n
    let α := WidePushoutShape.Hom.init n
    have : Mono (D.map α) := inferInstance
    have : Mono (F.map (D.map α)) := F.map_mono _
    have : Mono (G.map (D.map α)) := G.map_mono _
    change monoPrecompositionEquivalences
      (equivalenceMappingCylinderCornerMap (t.app (D.obj none)) (t.app (D.obj (some n)))
        (F.map (D.map α)) (G.map (D.map α)) (t.naturality (D.map α)).symm)
    exact ⟨inferInstance, isPrecompositionEquivalence_equivalenceMappingCylinderCornerMap
      _ _ _ _ _ (ht none) (ht (some n))⟩
  apply (isPrecompositionEquivalence_iff_equivalenceMappingCylinderIn _).2
  apply (isPrecompositionEquivalence_iff_llp_boundaryTests _).2
  intro E Y p hp
  have : HasLiftingProperty (s'.app none) p :=
    (isPrecompositionEquivalence_iff_llp_boundaryTests _).1 h0 _ hp
  have : ∀ n, HasLiftingProperty (wideNatTransCornerMap s' n) p := by
    intro n
    have : Mono (wideNatTransCornerMap s' n) := (hCorners n).1
    exact (isPrecompositionEquivalence_iff_llp_boundaryTests _).1 (hCorners n).2 _ hp
  exact hasLiftingProperty_of_widePushout_relative_corners s' cF cH hcF hcH (s.app c.pt) hi p


end SerrePositivity.InfinityCategories
