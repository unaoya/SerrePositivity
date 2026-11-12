module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.ReplacementSquareResolution
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.RelativePathEndpointCorner

/-!
概要：比較四角形の同時解像の始点側の比較。
方針：入れ子の pullback を合成の path 置換と同定し、相対 path の持ち上げを移す。
規約：元の基底への射と指定された始点を厳密に保つ。
使われ方：比較立方体の共通の解像からの一方の射を全境界持ち上げにする。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial

/-- 基底の path 置換を始域の射で引き戻すと、合成の path 置換となる。 -/
lemma replacementSquareStart_isPullback {A B X Y : SSet.{u}} (u : A ⟶ X) (v : B ⟶ Y)
    (p : A ⟶ B) (q : X ⟶ Y) (h : u ≫ q = p ≫ v) :
    IsPullback
      (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection v) p ≫
        pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 0) v)
      (pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection v) p)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 0) (u ≫ q) := by
  rw [h]
  exact (IsPullback.of_hasPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection v) p).paste_horiz
    (IsPullback.of_hasPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 0) v)

/-- 始点側の比較の標的と、合成の path 置換との厳密な同型。 -/
def replacementSquareStartTargetIso {A B X Y : SSet.{u}} (u : A ⟶ X) (v : B ⟶ Y)
    (p : A ⟶ B) (q : X ⟶ Y) (h : u ≫ q = p ≫ v) :
    pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection v) p ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacement (u ≫ q) :=
  (replacementSquareStart_isPullback u v p q h).isoPullback

/-- 同時解像を、元の始域と基底の path 置換の pullback へ写す。 -/
def replacementSquareStartCorner {A B X Y : SSet.{u}} (u : A ⟶ X) (v : B ⟶ Y)
    (p : A ⟶ B) (q : X ⟶ Y) (h : u ≫ q = p ≫ v) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacement u ⟶ pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection v) p :=
  pullback.lift (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.replacementSquareMap u v p q h) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection u)
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.replacementSquareMap_projection u v p q h)

/-- 始点側の比較を合成の置換で表示すると、端点を保つ既存の比較そのもの。 -/
lemma replacementSquareStartCorner_targetIso {A B X Y : SSet.{u}} (u : A ⟶ X) (v : B ⟶ Y)
    (p : A ⟶ B) (q : X ⟶ Y) (h : u ≫ q = p ≫ v) :
    replacementSquareStartCorner u v p q h ≫ (replacementSquareStartTargetIso u v p q h).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativePathEndpointCorner u q 0 := by
  have hf : (replacementSquareStartTargetIso u v p q h).hom ≫
      pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 0) (u ≫ q) =
        pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection v) p ≫
          pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 0) v :=
    (replacementSquareStart_isPullback u v p q h).isoPullback_hom_fst
  have hs : (replacementSquareStartTargetIso u v p q h).hom ≫
      pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 0) (u ≫ q) =
        pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection v) p :=
    (replacementSquareStart_isPullback u v p q h).isoPullback_hom_snd
  have hcf : replacementSquareStartCorner u v p q h ≫
      pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection v) p =
        _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.replacementSquareMap u v p q h := pullback.lift_fst _ _ _
  have hcs : replacementSquareStartCorner u v p q h ≫
      pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection v) p =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection u := pullback.lift_snd _ _ _
  apply pullback.hom_ext
  · rw [Category.assoc, hf, ← Category.assoc, hcf]
    have hl : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.replacementSquareMap u v p q h ≫
        pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 0) v =
          pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint X 0) u ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap q :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativePathSquareTargetMap_fst u v p q h 0
    have hr : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativePathEndpointCorner u q 0 ≫
        pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 0) (u ≫ q) =
          pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint X 0) u ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap q :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativePathSquareTargetMap_fst u (u ≫ q) (𝟙 A) q (by simp) 0
    exact hl.trans hr.symm
  · rw [Category.assoc, hs, hcs]
    symm
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativePathEndpointCorner, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacement,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathTargetAt, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection,
      Category.comp_id] using
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativePathSquareTargetMap_snd u (u ≫ q) (𝟙 A) q (by simp) 0)

/-- 相対可逆 path を持ち上げる下辺を持つ比較四角形の始点比較は全境界を持ち上げる。 -/
instance replacementSquareStartCorner_trivialKanFibration {A B X Y : SSet.{u}}
    (u : A ⟶ X) (v : B ⟶ Y) (p : A ⟶ B) (q : X ⟶ Y) (h : u ≫ q = p ≫ v)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathMapAt q 0)] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (replacementSquareStartCorner u v p q h) := by
  let e : Arrow.mk (replacementSquareStartCorner u v p q h) ≅
      Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativePathEndpointCorner u q 0) :=
    Arrow.isoMk (Iso.refl _) (replacementSquareStartTargetIso u v p q h) (by
      change (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacement u)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativePathEndpointCorner u q 0 =
        replacementSquareStartCorner u v p q h ≫ (replacementSquareStartTargetIso u v p q h).hom
      rw [Category.id_comp]
      exact (replacementSquareStartCorner_targetIso u v p q h).symm)
  exact ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.arrow_mk_iso_iff e).mpr
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativePathEndpointCorner u q 0))⟩

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial
