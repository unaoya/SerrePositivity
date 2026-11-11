module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalMappingPostEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalMappingPostcompositionLaws

/-!
概要：指定された族の厳密な面の等式を、元の端点固定 Hom 作用へ移す。
方針：同じ後合成の端点を正規化し、元の全区間族を展開する。
規約：元の族・元の射・元の面を選び直さない。
使われ方：同じ可逆比較三角形の全 Hom 作用と既存の各辺の作用の接続。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 端点を正規化した同じ Hom 後合成の普遍族を展開する。 -/
lemma intervalMappingPostOfEq_universal_uncurry {X Y : SSet.{u}} (f : X ⟶ Y)
    (x y : X _⦋0⦌) {x' y' : Y _⦋0⦌} (hx : f.app _ x = x') (hy : f.app _ y = y') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPostOfEq f x y hx hy) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y)) ≫ f := by
  simpa only [Category.id_comp] using _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPostOfEq_uncurry f x y hx hy (𝟙 _)

variable {A X Y : SSet.{u}} (P : A ⟶ X) (g : X ⟶ Y) (Q : A ⟶ Y)
  (h : P ≫ g = Q) (a b : A _⦋0⦌)

/-- 同じ族の指定された面への後合成を、元の端点の Hom へ正規化する。 -/
def intervalHomFamilyProjection :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (P.app _ a) (P.app _ b) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (Q.app _ a) (Q.app _ b) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPostOfEq g (P.app _ a) (P.app _ b)
    (congrArg (fun f : A ⟶ Y ↦ f.app (Opposite.op ⦋0⦌) a) h)
    (congrArg (fun f : A ⟶ Y ↦ f.app (Opposite.op ⦋0⦌) b) h)

/-- 同じ元の Hom 作用は、面への射影後に元の面の Hom 作用を厳密に回収する。 -/
lemma intervalHomFamilyProjection_factor :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPost P a b ≫ intervalHomFamilyProjection P g Q h a b =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPost Q a b := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective
  rw [intervalHomFamilyProjection, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPostOfEq_uncurry,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPost_universal_uncurry, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPost_universal_uncurry,
    Category.assoc, h]

/-- 同じ面の射が充満忠実なら、元の同じ Hom 射影は同値。 -/
lemma intervalHomFamilyProjection_isQCatEquivalence [Quasicategory X] [Quasicategory Y]
    (hg : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful g) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (intervalHomFamilyProjection P g Q h a b) :=
  hg.intervalMappingPostOfEq_isQCatEquivalence _ _ _ _

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
