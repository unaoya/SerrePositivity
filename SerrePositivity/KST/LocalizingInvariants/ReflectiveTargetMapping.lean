module

public import SerrePositivity.KST.LocalizingInvariants.IntervalFunctorMapFromHom
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.AdjunctionPinchedSpaces

/-!
概要：反射の左関手は、右随伴の像を終点とする元の写像空間に同値を誘導する。
方針：可逆余単位から導いた全パラメータの Hom 全単射で、区間模型の実逆を作る。
規約：指定した関手の pinchedHomMap そのもの。使われ方：Tamme の引き戻しの D 辺。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
  {F : X ⟶ Y} {G : Y ⟶ X} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G) (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful G)

include a hG in
lemma reflectiveTargetIntervalMap_equivalence (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFunctorMap F x (G.app (Opposite.op ⦋0⦌) y)) :=
  intervalFunctorMap_equivalence_of_constantHom_bijective F x _
    (fun A _ => reflectiveConstantPostMap_bijective a hG A x y)

include a hG in
lemma reflectiveTargetPinchedHomMap_equivalence (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap F x (G.app (Opposite.op ⦋0⦌) y)) := by
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_isQCatEquivalence x
    (G.app (Opposite.op ⦋0⦌) y)).comp
      (reflectiveTargetIntervalMap_equivalence a hG x y).isQCatEquivalence
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.pinchedIntervalComparison_naturality] at h
  exact ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_isQCatEquivalence (F.app (Opposite.op ⦋0⦌) x)
    (F.app (Opposite.op ⦋0⦌) (G.app (Opposite.op ⦋0⦌) y))).cancel_right h
  ).isSimplicialHomotopyEquivalence

end SerrePositivity.KST.LocalizingInvariants
