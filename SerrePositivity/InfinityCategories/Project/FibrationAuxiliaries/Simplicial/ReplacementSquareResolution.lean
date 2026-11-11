module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.RelativePathEquivalenceFibration

/-!
概要：比較四角形の可逆 path による同時解像と終点の比較。
方針：二つの同値の path 置換を可換四角形で結び、終点の pullback と比較する。
規約：単に射の合成の同値性だけでなく、元の可換四角形を保持する。
使われ方：span の三対象の同時置換による比較立方体。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial

/-- 可換四角形は、両側の可逆 path 置換の間の実際の射を誘導する。 -/
def replacementSquareMap {A B X Y : SSet.{u}} (u : A ⟶ X) (v : B ⟶ Y)
    (p : A ⟶ B) (q : X ⟶ Y) (h : u ≫ q = p ≫ v) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacement u ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacement v :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativePathSquareTargetMap u v p q h 0

/-- 四角形の置換は、元の始域への射影を保つ。 -/
lemma replacementSquareMap_projection {A B X Y : SSet.{u}} (u : A ⟶ X) (v : B ⟶ Y)
    (p : A ⟶ B) (q : X ⟶ Y) (h : u ≫ q = p ≫ v) :
    replacementSquareMap u v p q h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection v =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection u ≫ p :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativePathSquareTargetMap_snd u v p q h 0

/-- 四角形の置換は、終点での比較を厳密に保つ。 -/
lemma replacementSquareMap_endpoint {A B X Y : SSet.{u}} (u : A ⟶ X) (v : B ⟶ Y)
    (p : A ⟶ B) (q : X ⟶ Y) (h : u ≫ q = p ≫ v) :
    replacementSquareMap u v p q h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap v =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap u ≫ q := by
  have hf : replacementSquareMap u v p q h ≫
      pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 0) v =
        pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint X 0) u ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap q :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativePathSquareTargetMap_fst u v p q h 0
  change replacementSquareMap u v p q h ≫
    (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 0) v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 1) = _
  rw [← Category.assoc, hf, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap_endpoint, ← Category.assoc]
  rfl

/-- 置換された四角形を、元の終点と基底の置換の pullback へ写す。 -/
def replacementSquareEndCorner {A B X Y : SSet.{u}} (u : A ⟶ X) (v : B ⟶ Y)
    (p : A ⟶ B) (q : X ⟶ Y) (h : u ≫ q = p ≫ v) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacement u ⟶ pullback q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap v) :=
  pullback.lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap u) (replacementSquareMap u v p q h)
    (replacementSquareMap_endpoint u v p q h).symm

/-- 終点の比較の第一成分は、元の同値の path 置換の終点射。 -/
lemma replacementSquareEndCorner_fst {A B X Y : SSet.{u}} (u : A ⟶ X) (v : B ⟶ Y)
    (p : A ⟶ B) (q : X ⟶ Y) (h : u ≫ q = p ≫ v) :
    replacementSquareEndCorner u v p q h ≫
        pullback.fst q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap v) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap u :=
  pullback.lift_fst _ _ _

/-- 終点の比較の第二成分は、可換四角形の path 置換の射そのもの。 -/
lemma replacementSquareEndCorner_snd {A B X Y : SSet.{u}} (u : A ⟶ X) (v : B ⟶ Y)
    (p : A ⟶ B) (q : X ⟶ Y) (h : u ≫ q = p ≫ v) :
    replacementSquareEndCorner u v p q h ≫
        pullback.snd q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap v) = replacementSquareMap u v p q h :=
  pullback.lift_snd _ _ _

/-- 四角形の二つの横射が同値なら、その同時解像の終点の比較も同値。 -/
lemma replacementSquareEndCorner_isQCatEquivalence {A B X Y : SSet.{u}}
    [Quasicategory A] [Quasicategory B] [Quasicategory X] [Quasicategory Y]
    (u : A ⟶ X) (v : B ⟶ Y) (p : A ⟶ B) (q : X ⟶ Y) (h : u ≫ q = p ≫ v)
    (hu : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence u) (hv : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence v) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (replacementSquareEndCorner u v p q h) := by
  have ht := hv.equivalencePathReplacementMap_trivialKanFibration
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (pullback.fst q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap v)) :=
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.pullback_fst _ _ ht.mem⟩
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration
    (pullback.fst q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap v))).cancel_right
  rw [replacementSquareEndCorner_fst]
  have := hu.equivalencePathReplacementMap_trivialKanFibration
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration _

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial
