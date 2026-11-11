module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionRelativeLifting
public import Mathlib.CategoryTheory.LiftingProperties.Over
public import Mathlib.CategoryTheory.LiftingProperties.Adjunction

/-!
概要：slice の左随伴の内ホーン上の前合成同値を全 inner anodyne 射へ拡張する。
方針：前合成による検査射の右随伴が inner fibration となることを示し、持ち上げ性を往復する。
規約：モデル構造や弱飽和性の追加の仮定は不要。
使われ方：Kerodon Lemma 5.3.6.6（Tag 02RK）、left fibration に沿う逆像の平坦性。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：slice 内の全内ホーンの持ち上げ性から元の射は inner fibration。
方針：単体集合の正方形を下辺で指定した底上の正方形にする。
規約：底 B は任意。
使われ方：右随伴による持ち上げ問題の検査。 -/
lemma innerFibration_of_over_innerHorn_lifting {B : SSet.{u}} {X Y : Over B} (q : X ⟶ Y)
    (hq : ∀ {A D : Over B} (i : A ⟶ D), innerHornInclusions i.left →
      HasLiftingProperty i q) : InnerFibration q.left := by
  constructor
  intro A D i hi
  constructor
  intro a b hs
  let D' : Over B := Over.mk (b ≫ Y.hom)
  let A' : Over B := Over.mk (i ≫ b ≫ Y.hom)
  let i' : A' ⟶ D' := Over.homMk i
  let a' : A' ⟶ X := Over.homMk a (by
    change a ≫ X.hom = i ≫ b ≫ Y.hom
    rw [← Over.w q, ← Category.assoc, hs.w, Category.assoc])
  let b' : D' ⟶ Y := Over.homMk b
  have := hq i' hi
  have hs' : CommSq a' i' q b' := ⟨by apply Over.OverMorphism.ext; exact hs.w⟩
  refine CommSq.HasLift.mk' { l := hs'.lift.left, fac_left := ?_, fac_right := ?_ }
  · exact congrArg (fun k ↦ k.left) hs'.fac_left
  · exact congrArg (fun k ↦ k.left) hs'.fac_right

/-- 概要：単射を保つ左随伴が全内ホーンを前合成同値へ送れば全 inner anodyne 射も送る。
方針：各境界の前合成射を右随伴で inner fibration に移し、持ち上げ性を随伴で戻す。
規約：随伴は通常の slice と単体集合の圏の間のもの。
使われ方：生成ホーンの逆像の比較から一般の inner anodyne の逆像へ進む。 -/
lemma innerAnodyne_leftAdjoint_isPrecompositionEquivalence {B : SSet.{u}}
    {L : Over B ⥤ SSet.{u}} {R : SSet.{u} ⥤ Over B} (adj : L ⊣ R)
    [L.PreservesMonomorphisms]
    (hL : ∀ {A D : Over B} (i : A ⟶ D), innerHornInclusions i.left →
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (L.map i))
    {A D : Over B} (i : A ⟶ D) (hi : innerAnodyneExtensions i.left) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (L.map i) := by
  intro X hX
  have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration ((pre (L.map i)).app X) := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).2
    intro n
    let q := (pre (boundary n).ι).app X
    have hr : InnerFibration (R.map q).left := by
      apply innerFibration_of_over_innerHorn_lifting
      intro A' D' j hj
      have hm : ∀ {U V : SSet.{u}} (f : U ⟶ V), innerHornInclusions f → Mono f := by
        intro U V f hf
        cases hf
        infer_instance
      have : Mono j.left := hm _ hj
      have : Mono j := (Over.forget B).mono_of_mono_map (show Mono j.left from inferInstance)
      have : HasLiftingProperty (L.map j) q :=
        (hL j hj).hasLiftingProperty_pre (boundary n).ι X
      exact (adj.hasLiftingProperty_iff j q).1 inferInstance
    have : HasLiftingProperty i.left (R.map q).left :=
      hi (R.map q).left (InnerFibration.mem (q := (R.map q).left))
    have := HasLiftingProperty.over i (R.map q)
    have : HasLiftingProperty (L.map i) q :=
      (adj.hasLiftingProperty_iff i q).2 inferInstance
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.hasLiftingProperty_pre_iff_swapped (L.map i) (boundary n).ι X).1 inferInstance
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
